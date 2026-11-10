module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.AffineFpqcChartDescent
public import StacksFrontier.AlgebraicGeometry.Stacks.IsomGroupSpace
public import StacksFrontier.AlgebraicGeometry.Stacks.IsomSpaceFpqcSheaf
public import StacksFrontier.AlgebraicGeometry.Stacks.Points
public import StacksFrontier.AlgebraicGeometry.Stacks.QuasiCompactPointRepresentative
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativeAutomorphismSequence
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Torsors.UnitTorsorsOfInvertibleModules

/-!
# Automorphism groups at a point and extension of the ground field (Stacks 0DTT, 0DTV)

Let `𝒳` be an algebraic stack over a scheme `S` of a big fppf site and let `x ∈|𝒳|` be a point.
A field-valued representative `x : Spec k → 𝒳` of the point carries its *automorphism group
algebraic space* `G_x/k = Isom_𝒳(x, x)`, which is `AlgebraicGeometry.Stack.isomSpace` and is an
algebraic space over `Spec k` by `AlgebraicGeometry.Stack.isAlgebraicSpace_isomSpace`.

If `k'/k` is an extension of fields and `x'` is the induced morphism `Spec k' → 𝒳`, then `G_{x'}`
is the base change of `G_x` along `Spec k' → Spec k`; this is
`AlgebraicGeometry.Stack.isomSpaceBaseChange`, the key computation of this file. Since any two
field-valued representatives of one point of `|𝒳|` admit a common refinement, a property `P` of
algebraic spaces over fields which is invariant under extension of the ground field holds for
`G_x/k` at one representative exactly when it holds at every representative. That is
**Stacks 0DTT**.

The same base change carries a 1-morphism `f : 𝒳 ⟶ 𝒴` of algebraic stacks: writing `y = f ∘ x`,
the map `G_x ⟶ G_y` of automorphism group algebraic spaces is
`AlgebraicGeometry.Stack.pointAutomorphismSpaceMap`, and the map at a refinement `x'` of `x` is
the base change of the map at `x`. Being an isomorphism is fpqc local on the target
(**Stacks 041Y**) and a morphism of field spectra is a surjective, flat and quasi-compact
covering, so the condition passes both ways between a representative and a refinement; since
two representatives of one point have a common refinement, `G_x ⟶ G_y` is an isomorphism for
one representative exactly when it is for every representative. That is **Stacks 0DTV**.

The base change statement is proved at the level of fibred categories. For a fibred category `p`,
an object `x` of the fibre over `U` and a cartesian morphism `m : x' ⟶ x` over `e : V ⟶ U`, the
chosen pullback of `x'` along `g : W ⟶ V` and the chosen pullback of `x` along `g ≫ e` are two
cartesian lifts of `g ≫ e` at `x`, hence canonically isomorphic in the fibre over `W`
(`CategoryTheory.Functor.pullbackFiberBaseChangeIso`); conjugating by that isomorphism identifies
the sections of `Isom(x', x')` over `W` with the sections of `Isom(x, x)` over `g ≫ e`, compatibly
with restriction. The passage from the slice `𝒮/U` to the big fppf site of `U` is the Mathlib
comparison `CategoryTheory.Over.iteratedSliceEquivOverMapIso`.

## Main definitions

* `CategoryTheory.Functor.fiberEndConj`: conjugation of the endomorphisms of an object of a fibre
  by an isomorphism of that fibre.
* `CategoryTheory.Functor.pullbackFiberBaseChangeIso`: the comparison, in the fibre over `W`, of
  the chosen pullback of `x'` along `g` with the chosen pullback of `x` along `g ≫ e`.
* `CategoryTheory.Functor.isomPresheafBaseChange`: `Isom(x', x')` is the base change of
  `Isom(x, x)` along `e`, as presheaves on the slice categories.
* `AlgebraicGeometry.Stack.pointAutomorphismSpace`: `G_x/k`, the automorphism group algebraic
  space of a field-valued point.
* `AlgebraicGeometry.Stack.IsInvariantUnderGroundFieldExtension`: a property of algebraic spaces
  over fields is invariant under extension of the ground field.
* `AlgebraicGeometry.Stack.pointAutomorphismSpaceMap`: the map `G_x ⟶ G_y` of automorphism group
  algebraic spaces induced by a 1-morphism of algebraic stacks, where `y = f ∘ x`.

## Main results

* `AlgebraicGeometry.Stack.isomSpaceBaseChange`: the automorphism group algebraic space of a
  field-valued point is carried to the one of a refinement by base change.
* `AlgebraicGeometry.Stack.pointAutomorphismSpace_iff_of_hom`: a ground-field-invariant property
  of the automorphism group algebraic space is unchanged by refining a field-valued point.
* `AlgebraicGeometry.Stack.exists_pointAutomorphismSpace_iff_forall`: **Stacks 0DTT**.
* `CategoryTheory.Functor.morPresheafMap_app_fiberEndConj`: applying a 1-morphism of fibred
  categories commutes with base change on the sections of `Mor(x, x)`.
* `AlgebraicGeometry.Space.isIso_of_bijective_app_over_of_isSheaf_fpqc`: a morphism of fpqc
  sheaves on the big fppf site which is bijective on the sections over the objects lying over a
  surjective, flat and quasi-compact object is an isomorphism.
* `AlgebraicGeometry.Stack.isIso_pointAutomorphismSpaceMap_of_hom` and
  `AlgebraicGeometry.Stack.isIso_pointAutomorphismSpaceMap_of_hom'`: `G_x ⟶ G_y` is an
  isomorphism at a field-valued point exactly when it is at a refinement of it.
* `AlgebraicGeometry.Stack.exists_isIso_pointAutomorphismSpaceMap_iff_forall`:
  **Stacks 0DTV**.

## Implementation notes

The comparison `CategoryTheory.Functor.pullbackFiberBaseChangeIso` is pinned down by its
composite with the chosen cartesian lifts it compares, and every identity about it below is
proved from those factorizations, as in
`StacksFrontier.CategoryTheory.Sites.Descent.IsStack.PullbackFiberComp`. The two sides of such a
factorization are morphisms of the total category whose endpoints are spelled both through
`CategoryTheory.Functor.Fiber` and through `CategoryTheory.Functor.IsPreFibered.pullbackObj`;
these are definitionally equal but not syntactically so, which is why the proof of
`CategoryTheory.Functor.fiberEndConj_morRestrict` restates its goal with `change` before
rewriting.

Base change of a presheaf on the big fppf site of `U` along `e : V ⟶ U` is restriction along
`CategoryTheory.Over.map e.left`. The property `P` is therefore indexed by the object of the site
over which the algebraic space lives, and invariance asks that `P` be insensitive to that
restriction whenever both objects are spectra of fields.

The equivalence of Stacks 0DTT is stated for the representatives of a fixed point of `|𝒳|`
(`AlgebraicGeometry.Stack.points`), whose equality is the existence of a common field-valued
refinement by `AlgebraicGeometry.Stack.class_eq_class_iff_hasCommonExtension`; that refinement is
what the two applications of invariance are made along, and it is also what Stacks 0DTV passes
through.

Stacks 041Y is used through its sheaf-theoretic content rather than as the morphism property
`AlgebraicGeometry.Space.isomorphisms_isLocalAtTarget_fpqc`: the two automorphism group spaces
are presheaves on the big fppf site of the field spectrum, they are fpqc sheaves by
`AlgebraicGeometry.Stack.isSheaf_fpqc_isomSpace_of_isAlgebraicStack` (Stacks 0APL through
Stacks 045G), and a morphism between fpqc sheaves which is bijective on the sections over a
covering family is bijective on all sections. The covering family of an object `T` of the site
is the base change of the morphism of field spectra, which is surjective, flat and
quasi-compact, hence an fpqc covering by
`AlgebraicGeometry.Space.sieve_generate_singleton_mem_fpqcTopology_over`.

Only bijectivity of the sections is transported, never the base-change isomorphism of
presheaves itself: the comparison square for
`CategoryTheory.Functor.isomPresheafBaseChange` against a 1-morphism commutes component by
component, and `CategoryTheory.Presheaf.bijective_app_of_iso` moves the question across the
iterated-slice comparison, so no naturality of the whole square has to be assembled.

## References

* [Stacks Project, Tag 0DTT](https://stacks.math.columbia.edu/tag/0DTT)
* [Stacks Project, Tag 0DTV](https://stacks.math.columbia.edu/tag/0DTV)
* [Stacks Project, Tag 02ZB](https://stacks.math.columbia.edu/tag/02ZB)
* [Stacks Project, Tag 041Y](https://stacks.math.columbia.edu/tag/041Y)
* [Stacks Project, Tag 04XG](https://stacks.math.columbia.edu/tag/04XG)
* [Stacks Project, Tag 04YP](https://stacks.math.columbia.edu/tag/04YP)
-/

@[expose] public section

open CategoryTheory

namespace CategoryTheory.Over

universe v₁ u₁

/-- Restriction to a slice commutes with base change: for `e : V ⟶ U` in `C/X`, passing from
`C/V.left` to `(C/X)/U` either through `C/V` or through `C/U.left` gives naturally isomorphic
functors. This is Mathlib's `CategoryTheory.Over.iteratedSliceEquivOverMapIso` read in the
other direction, along the iterated slice equivalence. -/
def iteratedSliceBackwardMapIso {C : Type u₁} [Category.{v₁} C] {X : C} {U V : Over X}
    (e : V ⟶ U) :
    Over.iteratedSliceBackward V ⋙ Over.map e ≅
      Over.map e.left ⋙ Over.iteratedSliceBackward U :=
  (Functor.isoWhiskerLeft (Over.iteratedSliceBackward V)
      (Over.iteratedSliceEquivOverMapIso e)).symm ≪≫
    Functor.isoWhiskerRight (Over.iteratedSliceEquiv V).counitIso
      (Over.map e.left ⋙ Over.iteratedSliceBackward U)

end CategoryTheory.Over

namespace CategoryTheory.Functor

universe v₁ v₂ u₁ u₂ u₃

variable {𝒮 : Type u₁} [Category.{v₁} 𝒮] {𝒳 : Type u₂} [Category.{v₂} 𝒳]
  (p : 𝒳 ⥤ 𝒮) {U V : 𝒮}

attribute [local implicit_reducible] Fiber Fiber.fiberInclusion

/-- Conjugation by an isomorphism `a ≅ b` of a fibre identifies the endomorphisms of `a` with
those of `b`. -/
def fiberEndConj {W : 𝒮} {a b : p.Fiber W} (c : a ≅ b) : (a ⟶ a) ≃ (b ⟶ b) where
  toFun φ := c.inv ≫ φ ≫ c.hom
  invFun ψ := c.hom ≫ ψ ≫ c.inv
  left_inv φ := by simp
  right_inv ψ := by simp

/-- Conjugating by an isomorphism of a fibre preserves being an isomorphism. -/
lemma isIso_fiberEndConj {W : 𝒮} {a b : p.Fiber W} (c : a ≅ b) (φ : a ⟶ a) :
    IsIso (fiberEndConj p c φ) ↔ IsIso φ := by
  refine ⟨fun _ => ?_, fun _ => inferInstanceAs (IsIso (c.inv ≫ φ ≫ c.hom))⟩
  simpa [fiberEndConj] using (inferInstance : IsIso (c.hom ≫ fiberEndConj p c φ ≫ c.inv))

variable [p.IsFibered] (e : V ⟶ U) {x : p.Fiber U} {x' : p.Fiber V} (m : x'.1 ⟶ x.1)
  (hm : p.IsStronglyCartesian e m)

include hm

/-- The chosen cartesian lift of `g` at `x'`, followed by a cartesian morphism `x' ⟶ x` over `e`,
is a cartesian lift of `g ≫ e` at `x`. -/
lemma isCartesian_pullbackMap_comp_hom (g : Over V) :
    p.IsCartesian (g.hom ≫ e) (IsPreFibered.pullbackMap x'.2 g.hom ≫ m) := by
  have := hm
  infer_instance

/-- The comparison, in the fibre over `g.left`, between the chosen pullback of `x'` along `g` and
the chosen pullback of `x` along `g ≫ e`: both carry a cartesian morphism to `x` over `g ≫ e`. -/
noncomputable def pullbackFiberBaseChangeIso (g : Over V) :
    pullbackFiber p x' g.hom ≅ pullbackFiber p x (g.hom ≫ e) :=
  fiberIsoOfCartesian (g.hom ≫ e) (IsPreFibered.pullbackMap x'.2 g.hom ≫ m)
    (IsPreFibered.pullbackMap x.2 (g.hom ≫ e))
    (isCartesian_pullbackMap_comp_hom p e m hm g)
    (IsPreFibered.pullbackMap.IsCartesian x.2 (g.hom ≫ e))

/-- `CategoryTheory.Functor.pullbackFiberBaseChangeIso` followed by the chosen cartesian lift of
`g ≫ e` at `x` is the chosen cartesian lift of `g` at `x'` followed by `m`. -/
@[reassoc]
lemma pullbackFiberBaseChangeIso_hom_fac (g : Over V) :
    Fiber.fiberInclusion.map (pullbackFiberBaseChangeIso p e m hm g).hom ≫
        IsPreFibered.pullbackMap x.2 (g.hom ≫ e) =
      IsPreFibered.pullbackMap x'.2 g.hom ≫ m :=
  fiberIsoOfCartesian_hom_fac _ _ _ _ _

/-- The inverse of `CategoryTheory.Functor.pullbackFiberBaseChangeIso`, followed by the chosen
cartesian lift of `g` at `x'` and by `m`, is the chosen cartesian lift of `g ≫ e` at `x`. -/
@[reassoc]
lemma pullbackFiberBaseChangeIso_inv_fac (g : Over V) :
    Fiber.fiberInclusion.map (pullbackFiberBaseChangeIso p e m hm g).inv ≫
        IsPreFibered.pullbackMap x'.2 g.hom ≫ m =
      IsPreFibered.pullbackMap x.2 (g.hom ≫ e) :=
  fiberIsoOfCartesian_inv_fac _ _ _ _ _

/-- The comparisons of `CategoryTheory.Functor.pullbackFiberBaseChangeIso` are compatible with
the restriction maps of the chosen pullbacks. -/
@[reassoc]
lemma pullbackFiberBaseChangeIso_naturality {g₁ g₂ : Over V} (h : g₁ ⟶ g₂) :
    Fiber.fiberInclusion.map (pullbackFiberBaseChangeIso p e m hm g₁).hom ≫
        pullbackFiberMap p x ((Over.map e).map h) =
      pullbackFiberMap p x' h ≫
        Fiber.fiberInclusion.map (pullbackFiberBaseChangeIso p e m hm g₂).hom := by
  have h2 : p.IsHomLift h.left (pullbackFiberMap p x ((Over.map e).map h)) :=
    pullbackFiberMap_isHomLift p x ((Over.map e).map h)
  have hl : p.IsHomLift h.left
      (Fiber.fiberInclusion.map (pullbackFiberBaseChangeIso p e m hm g₁).hom ≫
        pullbackFiberMap p x ((Over.map e).map h)) := by
    have h0 : p.IsHomLift (𝟙 g₁.left ≫ h.left)
        (Fiber.fiberInclusion.map (pullbackFiberBaseChangeIso p e m hm g₁).hom ≫
          pullbackFiberMap p x ((Over.map e).map h)) := inferInstance
    rwa [Category.id_comp] at h0
  have hr : p.IsHomLift h.left
      (pullbackFiberMap p x' h ≫
        Fiber.fiberInclusion.map (pullbackFiberBaseChangeIso p e m hm g₂).hom) := by
    have h0 : p.IsHomLift (h.left ≫ 𝟙 g₂.left)
        (pullbackFiberMap p x' h ≫
          Fiber.fiberInclusion.map (pullbackFiberBaseChangeIso p e m hm g₂).hom) :=
      inferInstance
    rwa [Category.comp_id] at h0
  refine IsStronglyCartesian.ext p (g₂.hom ≫ e)
    (IsPreFibered.pullbackMap x.2 (g₂.hom ≫ e)) h.left ?_
  rw [Category.assoc, Category.assoc, show pullbackFiberMap p x ((Over.map e).map h) ≫
      IsPreFibered.pullbackMap x.2 (g₂.hom ≫ e) =
      IsPreFibered.pullbackMap x.2 (g₁.hom ≫ e) from pullbackFiberMap_fac p x _,
    pullbackFiberBaseChangeIso_hom_fac, pullbackFiberBaseChangeIso_hom_fac,
    ← Category.assoc, pullbackFiberMap_fac]

/-- `CategoryTheory.Functor.pullbackFiberBaseChangeIso_naturality` for the inverse
comparisons. -/
@[reassoc]
lemma pullbackFiberBaseChangeIso_inv_naturality {g₁ g₂ : Over V} (h : g₁ ⟶ g₂) :
    pullbackFiberMap p x ((Over.map e).map h) ≫
        Fiber.fiberInclusion.map (pullbackFiberBaseChangeIso p e m hm g₂).inv =
      Fiber.fiberInclusion.map (pullbackFiberBaseChangeIso p e m hm g₁).inv ≫
        pullbackFiberMap p x' h := by
  rw [show Fiber.fiberInclusion.map (pullbackFiberBaseChangeIso p e m hm g₂).inv =
      (Fiber.fiberInclusion.mapIso (pullbackFiberBaseChangeIso p e m hm g₂)).inv from rfl,
    show Fiber.fiberInclusion.map (pullbackFiberBaseChangeIso p e m hm g₁).inv =
      (Fiber.fiberInclusion.mapIso (pullbackFiberBaseChangeIso p e m hm g₁)).inv from rfl,
    Iso.comp_inv_eq, Category.assoc, Iso.eq_inv_comp]
  exact pullbackFiberBaseChangeIso_naturality p e m hm h

/-- Conjugating by `CategoryTheory.Functor.pullbackFiberBaseChangeIso` commutes with restricting
a section of the presheaf of morphisms. -/
lemma fiberEndConj_morRestrict {g₁ g₂ : Over V} (h : g₁ ⟶ g₂)
    (φ : pullbackFiber p x' g₂.hom ⟶ pullbackFiber p x' g₂.hom) :
    fiberEndConj p (pullbackFiberBaseChangeIso p e m hm g₁) (morRestrict p x' x' h φ) =
      morRestrict p x x ((Over.map e).map h)
        (fiberEndConj p (pullbackFiberBaseChangeIso p e m hm g₂) φ) := by
  refine morRestrict_uniq p x x ((Over.map e).map h)
    (fiberEndConj p (pullbackFiberBaseChangeIso p e m hm g₂) φ)
    (fiberEndConj p (pullbackFiberBaseChangeIso p e m hm g₁)
      (morRestrict p x' x' h φ)) ?_
  change Fiber.fiberInclusion.map ((pullbackFiberBaseChangeIso p e m hm g₁).inv ≫
        morRestrict p x' x' h φ ≫ (pullbackFiberBaseChangeIso p e m hm g₁).hom) ≫
      IsPreFibered.pullbackMap x.2 (g₁.hom ≫ e) =
    pullbackFiberMap p x ((Over.map e).map h) ≫
      Fiber.fiberInclusion.map ((pullbackFiberBaseChangeIso p e m hm g₂).inv ≫ φ ≫
        (pullbackFiberBaseChangeIso p e m hm g₂).hom) ≫
        IsPreFibered.pullbackMap x.2 (g₂.hom ≫ e)
  simp only [Functor.map_comp, Category.assoc, pullbackFiberBaseChangeIso_hom_fac,
    morRestrict_fac_assoc, pullbackFiberBaseChangeIso_inv_naturality_assoc]

/-- **`Isom(x', x')` is the base change of `Isom(x, x)`.** If `m : x' ⟶ x` is a cartesian
morphism of a fibred category over `e : V ⟶ U`, then the presheaf of automorphisms of `x'` on
`𝒮/V` is the restriction along `CategoryTheory.Over.map e` of the presheaf of automorphisms of
`x` on `𝒮/U`. -/
noncomputable def isomPresheafBaseChange :
    p.isomPresheaf x' x' ≅ (Over.map e).op ⋙ p.isomPresheaf x x :=
  NatIso.ofComponents
    (fun g => Equiv.toIso (Equiv.subtypeEquiv
      (fiberEndConj p (pullbackFiberBaseChangeIso p e m hm g.unop))
      (fun φ => (isIso_fiberEndConj p (pullbackFiberBaseChangeIso p e m hm g.unop)
        (show pullbackFiber p x' g.unop.hom ⟶ pullbackFiber p x' g.unop.hom from φ)).symm)))
    (by
      intro g g' q
      ext φ
      exact Subtype.ext (fiberEndConj_morRestrict p e m hm q.unop
        (show pullbackFiber p x' g.unop.hom ⟶ pullbackFiber p x' g.unop.hom from φ.1)))

section OneMorphism

variable {𝒴 : Type u₃} [Category.{v₂} 𝒴] {r : 𝒴 ⥤ 𝒮} [r.IsFibered] {G : 𝒳 ⥤ 𝒴}
  (hG : IsFibredOneMorphism p r G)

/-- The base-change comparison of `CategoryTheory.Functor.pullbackFiberBaseChangeIso` for the
image of `m : x' ⟶ x` under a 1-morphism `G` of fibred categories, which is again cartesian. -/
noncomputable abbrev mapPullbackFiberBaseChangeIso (g : Over V) :
    pullbackFiber r ((fiberFunctorOfCompEq hG.comp_eq V).obj x') g.hom ≅
      pullbackFiber r ((fiberFunctorOfCompEq hG.comp_eq U).obj x) (g.hom ≫ e) :=
  pullbackFiberBaseChangeIso r e
    (x := (fiberFunctorOfCompEq hG.comp_eq U).obj x)
    (x' := (fiberFunctorOfCompEq hG.comp_eq V).obj x')
    (G.map m) (hG.map_isStronglyCartesian e m hm) g

/-- **A 1-morphism of fibred categories carries the base-change comparison to the base-change
comparison.** Both composites are morphisms of the fibre over `g.left` from the chosen pullback
of `G x'` to the image of the chosen pullback of `x` along `g ≫ e`, and both become the chosen
cartesian lift of `g` at `G x'` followed by `G m` after composing with the image of the chosen
cartesian lift of `g ≫ e` at `x`. -/
lemma mapPullbackFiberIso_comp_map_pullbackFiberBaseChangeIso (g : Over V) :
    (hG.mapPullbackFiberIso x' g.hom).hom ≫
        (fiberFunctorOfCompEq hG.comp_eq g.left).map
          (pullbackFiberBaseChangeIso p e m hm g).hom =
      (mapPullbackFiberBaseChangeIso p e m hm hG g).hom ≫
        (hG.mapPullbackFiberIso x (g.hom ≫ e)).hom := by
  have hcart : r.IsCartesian (g.hom ≫ e)
      (G.map (IsPreFibered.pullbackMap x.2 (g.hom ≫ e))) :=
    hG.isCartesian_map_pullbackMap x (g.hom ≫ e)
  apply Fiber.hom_ext
  refine IsCartesian.ext r (g.hom ≫ e) (G.map (IsPreFibered.pullbackMap x.2 (g.hom ≫ e)))
    _ _ ?_
  rw [Functor.map_comp, Functor.map_comp, Category.assoc, Category.assoc,
    fiberInclusion_map_fiberFunctorOfCompEq_map, ← Functor.map_comp,
    pullbackFiberBaseChangeIso_hom_fac, Functor.map_comp]
  conv_lhs => rw [← Category.assoc, IsFibredOneMorphism.mapPullbackFiberIso_hom_fac]
  rw [IsFibredOneMorphism.mapPullbackFiberIso_hom_fac,
    pullbackFiberBaseChangeIso_hom_fac]

/-- **Applying a 1-morphism commutes with base change on the sections of `Mor(x, x)`.** The
square of `CategoryTheory.Functor.IsFibredOneMorphism.morPresheafMap` against the two
base-change comparisons commutes. -/
lemma morPresheafMap_app_fiberEndConj (g : Over V)
    (φ : pullbackFiber p x' g.hom ⟶ pullbackFiber p x' g.hom) :
    fiberEndConj r (mapPullbackFiberBaseChangeIso p e m hm hG g)
        ((hG.morPresheafMap x' x').app (Opposite.op g) φ) =
      (hG.morPresheafMap x x).app (Opposite.op ((Over.map e).obj g))
        (fiberEndConj p (pullbackFiberBaseChangeIso p e m hm g) φ) := by
  set T := fiberFunctorOfCompEq hG.comp_eq g.left
  set c := pullbackFiberBaseChangeIso p e m hm g
  set A := hG.mapPullbackFiberIso x' g.hom
  set I := hG.mapPullbackFiberIso x (g.hom ≫ e)
  set Cr := mapPullbackFiberBaseChangeIso p e m hm hG g
  have key : A.hom ≫ T.map c.hom = Cr.hom ≫ I.hom :=
    mapPullbackFiberIso_comp_map_pullbackFiberBaseChangeIso p e m hm hG g
  have key₁ : Cr.inv ≫ A.hom = I.hom ≫ T.map c.inv := by
    rw [Iso.inv_comp_eq, ← Category.assoc, ← key, Category.assoc, ← T.map_comp,
      c.hom_inv_id, T.map_id, Category.comp_id]
  have key₂ : A.inv ≫ Cr.hom = T.map c.hom ≫ I.inv := by
    rw [Iso.eq_comp_inv, Category.assoc, ← key, ← Category.assoc, A.inv_hom_id,
      Category.id_comp]
  change Cr.inv ≫ (A.hom ≫ T.map φ ≫ A.inv) ≫ Cr.hom =
    I.hom ≫ T.map (c.inv ≫ φ ≫ c.hom) ≫ I.inv
  simp only [T.map_comp, Category.assoc]
  rw [reassoc_of% key₁, key₂]

end OneMorphism

end CategoryTheory.Functor

namespace CategoryTheory.Presheaf

universe v₃ u₄

/-- Bijectivity of a component of a morphism of presheaves of types only depends on the object
up to isomorphism: the restriction maps along an isomorphism are bijections. -/
theorem bijective_app_of_iso {𝒞 : Type u₄} [Category.{v₃} 𝒞] {F G : 𝒞ᵒᵖ ⥤ Type v₃}
    (φ : F ⟶ G) {a b : 𝒞} (θ : a ≅ b) (h : Function.Bijective (φ.app (Opposite.op b))) :
    Function.Bijective (φ.app (Opposite.op a)) := by
  have hFθ : Function.Bijective (F.map θ.hom.op) :=
    ConcreteCategory.bijective_of_isIso (F.map θ.hom.op)
  have hGθ : Function.Bijective (G.map θ.hom.op) :=
    ConcreteCategory.bijective_of_isIso (G.map θ.hom.op)
  have hcomp : (fun z => φ.app (Opposite.op a) (F.map θ.hom.op z)) =
      fun z => G.map θ.hom.op (φ.app (Opposite.op b) z) :=
    funext fun z => (NatTrans.naturality_apply φ θ.hom.op z)
  have hb : Function.Bijective (fun z => φ.app (Opposite.op a) (F.map θ.hom.op z)) := by
    rw [hcomp]
    exact hGθ.comp h
  exact (Function.Bijective.of_comp_iff _ hFθ).mp hb

end CategoryTheory.Presheaf

namespace AlgebraicGeometry.Space

open CategoryTheory

universe u

variable (B : BigFppfSite.{u}) (X : Scheme.{u}) (hX : B.Contains X)

/-- **A morphism of fpqc sheaves on the big fppf site of `X` which is bijective on the sections
over every object lying over a surjective, flat and quasi-compact object `d` is an
isomorphism.** The objects lying over `d` cover every object of the site, by base change of the
structure morphism of `d`, so the sheaf condition for that covering gives bijectivity on all
sections. -/
theorem isIso_of_bijective_app_over_of_isSheaf_fpqc
    {F G : (BigFppfOver B X hX)ᵒᵖ ⥤ Type u}
    (hF : Presheaf.IsSheaf
      ((Scheme.fpqcPrecoverage.comap (BigFppfOver.toScheme B X hX)).toGrothendieck) F)
    (hG : Presheaf.IsSheaf
      ((Scheme.fpqcPrecoverage.comap (BigFppfOver.toScheme B X hX)).toGrothendieck) G)
    (φ : F ⟶ G) (d : BigFppfOver B X hX)
    (hds : Surjective (B.inclusion.map d.hom))
    (hdf : Flat (B.inclusion.map d.hom))
    (hdc : QuasiCompact (B.inclusion.map d.hom))
    (hbij : ∀ (T : BigFppfOver B X hX) (_ : T ⟶ d),
      Function.Bijective (φ.app (Opposite.op T))) :
    IsIso φ := by
  rw [NatTrans.isIso_iff_isIso_app]
  rintro ⟨T⟩
  refine (ConcreteCategory.isIso_iff_bijective _).2 ?_
  have hsq : IsPullback (B.inclusion.map (Limits.pullback.fst T.hom d.hom))
      (B.inclusion.map (Limits.pullback.snd T.hom d.hom))
      (B.inclusion.map T.hom) (B.inclusion.map d.hom) :=
    (IsPullback.of_hasPullback T.hom d.hom).map B.inclusion
  have hu : Limits.pullback.snd T.hom d.hom ≫ d.hom =
      Limits.pullback.fst T.hom d.hom ≫ T.hom := Limits.pullback.condition.symm
  set q : (Over.mk (Limits.pullback.fst T.hom d.hom ≫ T.hom) :
    BigFppfOver B X hX) ⟶ T := Over.homMk (Limits.pullback.fst T.hom d.hom) rfl
  set u : (Over.mk (Limits.pullback.fst T.hom d.hom ≫ T.hom) :
    BigFppfOver B X hX) ⟶ d := Over.homMk (Limits.pullback.snd T.hom d.hom) hu
  have hqmap : (BigFppfOver.toScheme B X hX).map q =
      B.inclusion.map (Limits.pullback.fst T.hom d.hom) := rfl
  have hcov := sieve_generate_singleton_mem_fpqcTopology_over B X hX q
    (by rw [hqmap]; exact MorphismProperty.of_isPullback (P := @Surjective) hsq.flip hds)
    (by rw [hqmap]; exact MorphismProperty.of_isPullback (P := @Flat) hsq.flip hdf)
    (by rw [hqmap]; exact MorphismProperty.of_isPullback (P := @QuasiCompact) hsq.flip hdc)
  refine Stacks.Cohomology.Torsors.Generators.bijective_of_bijective_on_cover
    _ hF hG _ hcov φ ?_
  rintro W a ⟨Y, a₁, a₂, ⟨⟩, rfl⟩
  exact hbij W (a₁ ≫ u)

end AlgebraicGeometry.Space

namespace AlgebraicGeometry.Stack

open CategoryTheory

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Base change of the Isom algebraic space.** If `m : x' ⟶ x` is a cartesian morphism of a
category fibred in groupoids over `e : V ⟶ U`, then `Isom_𝒳(x', x')`, as an algebraic space over
`V`, is the base change of `Isom_𝒳(x, x)` along `e`. -/
noncomputable def isomSpaceBaseChange
    (𝒳 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS))
    {U V : BigFppfOver B S hS} (e : V ⟶ U)
    {x : 𝒳.val.p.Fiber U} {x' : 𝒳.val.p.Fiber V} (m : x'.1 ⟶ x.1)
    (hm : 𝒳.val.p.IsStronglyCartesian e m) :
    isomSpace B S hS 𝒳 V x' x' ≅ (Over.map e.left).op ⋙ isomSpace B S hS 𝒳 U x x :=
  letI : 𝒳.val.p.IsFibered := 𝒳.isFiberedInGroupoids.isFibered
  Functor.isoWhiskerLeft (Over.iteratedSliceBackward V).op
      (Functor.isomPresheafBaseChange 𝒳.val.p e m hm) ≪≫
    (Functor.isoWhiskerRight (NatIso.op (Over.iteratedSliceBackwardMapIso e))
      (𝒳.val.p.isomPresheaf x x)).symm

/-- The automorphism group algebraic space `G_x/k` of a field-valued point `x : Spec k → 𝒳`: the
algebraic space `Isom_𝒳(x, x)` over `Spec k`, by `AlgebraicGeometry.Stack.isomSpace`. -/
noncomputable abbrev pointAutomorphismSpace
    (𝒳 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS))
    (p : FieldValuedPoint B S hS 𝒳.val) :
    (BigFppfOver B p.base.left.1 p.base.left.2)ᵒᵖ ⥤ Type u :=
  isomSpace B S hS 𝒳 p.base (Functor.Fiber.mk p.over) (Functor.Fiber.mk p.over)

/-- `G_x/k` is an algebraic space over `Spec k`. -/
theorem isAlgebraicSpace_pointAutomorphismSpace
    (𝒳 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS))
    (h𝒳 : IsAlgebraicStack.{u, w} B S hS 𝒳.val)
    (p : FieldValuedPoint B S hS 𝒳.val) :
    IsAlgebraicSpace B p.base.left.1 p.base.left.2
      (pointAutomorphismSpace B S hS 𝒳 p) :=
  isAlgebraicSpace_isomSpace B S hS 𝒳 h𝒳 p.base _ _

/-- A property of algebraic spaces over fields — for each object `U` of the big fppf site of `S`,
a property of the algebraic spaces over `U` — is *invariant under ground field extensions* when,
for every morphism `e : V ⟶ U` between spectra of fields, it holds for an algebraic space over
`U` exactly when it holds for its base change along `e`. Base change along `e` is restriction
along `CategoryTheory.Over.map e.left`. -/
def IsInvariantUnderGroundFieldExtension
    (P : ∀ U : BigFppfOver B S hS, ((BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u) → Prop) :
    Prop :=
  ∀ {k l : Type u} [Field k] [Field l] (U V : BigFppfOver B S hS)
    (_hU : (BigFppfOver.toScheme B S hS).obj U ≅ Spec (.of k))
    (_hV : (BigFppfOver.toScheme B S hS).obj V ≅ Spec (.of l)) (e : V ⟶ U)
    (G : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u)
    (G' : (BigFppfOver B V.left.1 V.left.2)ᵒᵖ ⥤ Type u)
    (_hG : IsAlgebraicSpace B U.left.1 U.left.2 G)
    (_hG' : IsAlgebraicSpace B V.left.1 V.left.2 G'),
    Nonempty (G' ≅ (Over.map e.left).op ⋙ G) → (P U G ↔ P V G')

variable {𝒳 : AlgebraicStacks.{u, w} B S hS}

private lemma isStronglyCartesian_of_fieldValuedPointHom
    {𝒳 : AlgebraicStacks.{u, w} B S hS} {p t : FieldValuedPoint B S hS 𝒳.val.val}
    (a : t.obj ⟶ p.obj) :
    𝒳.val.val.p.IsStronglyCartesian (fieldValuedPointBaseMap B S hS a) a := by
  have hlift : 𝒳.val.val.p.IsHomLift (fieldValuedPointBaseMap B S hS a) a :=
    IsHomLift.of_fac' 𝒳.val.val.p (fieldValuedPointBaseMap B S hS a) a t.over p.over
      (by simp [fieldValuedPointBaseMap])
  exact 𝒳.val.isFiberedInGroupoids.isStronglyCartesian_homLift _ a

/-- A ground-field-invariant property of the automorphism group algebraic space is unchanged by
refining a field-valued point: an arrow `t ⟶ p` of field-valued points of `𝒳` exhibits `G_t` as
the base change of `G_p` along the corresponding extension of fields. -/
theorem pointAutomorphismSpace_iff_of_hom
    (P : ∀ U : BigFppfOver B S hS, ((BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u) → Prop)
    (hP : IsInvariantUnderGroundFieldExtension B S hS P)
    {p t : FieldValuedPoint B S hS 𝒳.val.val} (f : t.obj ⟶ p.obj) :
    P p.base (pointAutomorphismSpace B S hS 𝒳.val p) ↔
      P t.base (pointAutomorphismSpace B S hS 𝒳.val t) := by
  exact hP p.base t.base p.isSpec t.isSpec (fieldValuedPointBaseMap B S hS f) _ _
    (isAlgebraicSpace_pointAutomorphismSpace B S hS 𝒳.val 𝒳.property p)
    (isAlgebraicSpace_pointAutomorphismSpace B S hS 𝒳.val 𝒳.property t)
    ⟨isomSpaceBaseChange B S hS 𝒳.val _ f (isStronglyCartesian_of_fieldValuedPointHom B S hS f)⟩

/-- **Stacks 0DTT.** Let `𝒳` be an algebraic stack, let `q ∈ |𝒳|` be a point and let `P` be a
property of algebraic spaces over fields which is invariant under ground field extensions. Then
the automorphism group algebraic space `G_x/k` has `P` for *some* field-valued representative
`x : Spec k → 𝒳` of `q` if and only if it has `P` for *every* field-valued representative. -/
@[stacks 0DTT]
theorem exists_pointAutomorphismSpace_iff_forall
    (q : points B S hS 𝒳.val.val 𝒳.val.isFiberedInGroupoids)
    (P : ∀ U : BigFppfOver B S hS, ((BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u) → Prop)
    (hP : IsInvariantUnderGroundFieldExtension B S hS P) :
    (∃ p : FieldValuedPoint B S hS 𝒳.val.val,
        pointClass B S hS 𝒳.val.val 𝒳.val.isFiberedInGroupoids p = q ∧
        P p.base (pointAutomorphismSpace B S hS 𝒳.val p)) ↔
      ∀ p : FieldValuedPoint B S hS 𝒳.val.val,
        pointClass B S hS 𝒳.val.val 𝒳.val.isFiberedInGroupoids p = q →
        P p.base (pointAutomorphismSpace B S hS 𝒳.val p) := by
  constructor
  · rintro ⟨p, hp, hPp⟩ r hr
    obtain ⟨t, ⟨fp⟩, ⟨fr⟩⟩ :=
      (class_eq_class_iff_hasCommonExtension B S hS 𝒳.val.val
        𝒳.val.isFiberedInGroupoids p r).mp (hp.trans hr.symm)
    exact (pointAutomorphismSpace_iff_of_hom B S hS P hP fr).mpr
      ((pointAutomorphismSpace_iff_of_hom B S hS P hP fp).mp hPp)
  · intro h
    obtain ⟨p, hp⟩ := Quotient.exists_rep q
    exact ⟨p, hp, h p hp⟩

section AutomorphismGroupMap

variable {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS}

/-- The map `G_x ⟶ G_y` of automorphism group algebraic spaces induced by a 1-morphism
`f : 𝒳 ⟶ 𝒴` of algebraic stacks at a field-valued point `x : Spec k → 𝒳` and its image
`y = f ∘ x`. It applies `f` to a local automorphism of `x`. -/
noncomputable def pointAutomorphismSpaceMap (f : 𝒳 ⟶ 𝒴)
    (p : FieldValuedPoint B S hS 𝒳.val.val) :
    pointAutomorphismSpace B S hS 𝒳.val p ⟶
      isomSpace B S hS 𝒴.val p.base
        (imageFiberObj B S hS 𝒳.val 𝒴.val f.hom.hom p.base (Functor.Fiber.mk p.over))
        (imageFiberObj B S hS 𝒳.val 𝒴.val f.hom.hom p.base (Functor.Fiber.mk p.over)) :=
  isomSpaceMap B S hS 𝒳.val 𝒴.val f.hom.hom p.base _ _

private lemma bijective_iff_of_square {A₁ B₁ A₂ B₂ : Type*} {j : A₁ → B₁} {j' : A₂ → B₂}
    {α : A₁ → A₂} {β : B₁ → B₂} (hα : Function.Bijective α) (hβ : Function.Bijective β)
    (hcomm : ∀ z, β (j z) = j' (α z)) :
    Function.Bijective j ↔ Function.Bijective j' := by
  rw [← Function.Bijective.of_comp_iff j' hα,
    show j' ∘ α = β ∘ j from funext fun z => (hcomm z).symm,
    Function.Bijective.of_comp_iff' hβ]

/-- **Base change of the map of automorphism sheaves along a cartesian morphism.** If
`m : x' ⟶ x` is cartesian over `e : V ⟶ U`, then `f` is bijective on the `W`-sections of
`Isom_𝒳(x', x') ⟶ Isom_𝒴(f x', f x')` exactly when it is on the sections of
`Isom_𝒳(x, x) ⟶ Isom_𝒴(f x, f x)` over `W` read as an object over `U`. -/
private lemma bijective_isomSpaceMap_app_baseChange_iff
    (𝒳 𝒴 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS))
    (F : 𝒳.val ⥤ᵇ 𝒴.val) {U V : BigFppfOver B S hS} (e : V ⟶ U)
    {x : 𝒳.val.p.Fiber U} {x' : 𝒳.val.p.Fiber V} (m : x'.1 ⟶ x.1)
    (hm : 𝒳.val.p.IsStronglyCartesian e m)
    (W : (BigFppfOver B V.left.1 V.left.2)ᵒᵖ) :
    Function.Bijective ((isomSpaceMap B S hS 𝒳 𝒴 F V x' x').app W) ↔
      Function.Bijective ((isomSpaceMap B S hS 𝒳 𝒴 F U x x).app
        ((Over.map e.left).op.obj W)) := by
  have hfib𝒳 : 𝒳.val.p.IsFibered := 𝒳.isFiberedInGroupoids.isFibered
  have hfib𝒴 : 𝒴.val.p.IsFibered := 𝒴.isFiberedInGroupoids.isFibered
  have hFm := (isFibredOneMorphism_basedFunctor B S hS 𝒳 𝒴 F).map_isStronglyCartesian e m hm
  set g : Over V := (Over.iteratedSliceBackward V).obj W.unop with hg
  have hstep : Function.Bijective
      ((isomPresheafMap B S hS 𝒳 𝒴 F V x' x').app (Opposite.op g)) ↔
      Function.Bijective ((isomPresheafMap B S hS 𝒳 𝒴 F U x x).app
        (Opposite.op ((Over.map e).obj g))) := by
    refine bijective_iff_of_square
      (α := (Functor.isomPresheafBaseChange 𝒳.val.p e m hm).hom.app (Opposite.op g))
      (β := (Functor.isomPresheafBaseChange 𝒴.val.p e
        (x := imageFiberObj B S hS 𝒳 𝒴 F U x) (x' := imageFiberObj B S hS 𝒳 𝒴 F V x')
        (F.toFunctor.map m) hFm).hom.app (Opposite.op g))
      (ConcreteCategory.bijective_of_isIso _) (ConcreteCategory.bijective_of_isIso _) ?_
    intro φ
    exact Subtype.ext (Functor.morPresheafMap_app_fiberEndConj 𝒳.val.p e m hm
      (isFibredOneMorphism_basedFunctor B S hS 𝒳 𝒴 F) g φ.1)
  refine hstep.trans ⟨fun h => ?_, fun h => ?_⟩
  · exact Presheaf.bijective_app_of_iso (isomPresheafMap B S hS 𝒳 𝒴 F U x x)
      ((Over.iteratedSliceBackwardMapIso e).app W.unop).symm h
  · exact Presheaf.bijective_app_of_iso (isomPresheafMap B S hS 𝒳 𝒴 F U x x)
      ((Over.iteratedSliceBackwardMapIso e).app W.unop) h

/-- Bijectivity of the map of automorphism sheaves at a field-valued point, read at an object
of the site lying over the field spectrum of a refinement, is the same question at the
refinement. -/
private lemma bijective_pointAutomorphismSpaceMap_app_iff (f : 𝒳 ⟶ 𝒴)
    {p t : FieldValuedPoint B S hS 𝒳.val.val} (a : t.obj ⟶ p.obj)
    (W : (BigFppfOver B t.base.left.1 t.base.left.2)ᵒᵖ) :
    Function.Bijective ((pointAutomorphismSpaceMap B S hS f t).app W) ↔
      Function.Bijective ((pointAutomorphismSpaceMap B S hS f p).app
        ((Over.map (fieldValuedPointBaseMap B S hS a).left).op.obj W)) :=
  bijective_isomSpaceMap_app_baseChange_iff B S hS 𝒳.val 𝒴.val f.hom.hom
    (fieldValuedPointBaseMap B S hS a) a (isStronglyCartesian_of_fieldValuedPointHom B S hS a) W

/-- **Base change of the automorphism group map to an extension field.** If `f` induces an
isomorphism of automorphism group algebraic spaces at a field-valued point, it does so at every
refinement of that point: the map at the refinement is a base change of the map at the
point. -/
theorem isIso_pointAutomorphismSpaceMap_of_hom (f : 𝒳 ⟶ 𝒴)
    {p t : FieldValuedPoint B S hS 𝒳.val.val} (a : t.obj ⟶ p.obj)
    (h : IsIso (pointAutomorphismSpaceMap B S hS f p)) :
    IsIso (pointAutomorphismSpaceMap B S hS f t) := by
  rw [NatTrans.isIso_iff_isIso_app] at h ⊢
  intro W
  refine (ConcreteCategory.isIso_iff_bijective _).2 ?_
  exact (bijective_pointAutomorphismSpaceMap_app_iff B S hS f a W).mpr
    ((ConcreteCategory.isIso_iff_bijective _).1 (h _))

/-- The morphism of field spectra underlying an arrow of field-valued points is surjective, flat
and quasi-compact: it is a morphism of spectra of fields. -/
lemma surjective_flat_quasiCompact_fieldValuedPointBaseMap
    {𝒳 : AlgebraicStacks.{u, w} B S hS} {p t : FieldValuedPoint B S hS 𝒳.val.val}
    (a : t.obj ⟶ p.obj) :
    Surjective (B.inclusion.map (fieldValuedPointBaseMap B S hS a).left) ∧
      Flat (B.inclusion.map (fieldValuedPointBaseMap B S hS a).left) ∧
      QuasiCompact (B.inclusion.map (fieldValuedPointBaseMap B S hS a).left) := by
  set sm : Spec (.of t.carrier) ⟶ Spec (.of p.carrier) :=
    t.isSpec.inv ≫ B.inclusion.map (fieldValuedPointBaseMap B S hS a).left ≫ p.isSpec.hom
    with hsm
  obtain ⟨ψ, hψ⟩ := Spec.map_surjective sm
  have hs : Surjective sm := by
    rw [← hψ]
    infer_instance
  have hf : Flat sm := by
    rw [← hψ]
    infer_instance
  have hc : QuasiCompact sm := by
    rw [← hψ]
    infer_instance
  have heq : B.inclusion.map (fieldValuedPointBaseMap B S hS a).left =
      t.isSpec.hom ≫ sm ≫ p.isSpec.inv := by rw [hsm]; simp
  rw [heq]
  exact ⟨inferInstance, inferInstance, inferInstance⟩

/-- **Descent of the automorphism group map along an extension field.** If `f` induces an
isomorphism of automorphism group algebraic spaces at a refinement of a field-valued point, it
does so at the point itself: the map at the refinement is the base change of the map at the
point along a surjective, flat and quasi-compact morphism of field spectra, and being an
isomorphism is fpqc local on the target (**Stacks 041Y**), read here on the sections of the two
Isom sheaves. -/
theorem isIso_pointAutomorphismSpaceMap_of_hom' (f : 𝒳 ⟶ 𝒴)
    {p t : FieldValuedPoint B S hS 𝒳.val.val} (a : t.obj ⟶ p.obj)
    (h : IsIso (pointAutomorphismSpaceMap B S hS f t)) :
    IsIso (pointAutomorphismSpaceMap B S hS f p) := by
  obtain ⟨hs, hf, hc⟩ := surjective_flat_quasiCompact_fieldValuedPointBaseMap B S hS a
  rw [NatTrans.isIso_iff_isIso_app] at h
  refine Space.isIso_of_bijective_app_over_of_isSheaf_fpqc B p.base.left.1 p.base.left.2
    (isSheaf_fpqc_isomSpace_of_isAlgebraicStack B S hS 𝒳.val 𝒳.property p.base _ _)
    (isSheaf_fpqc_isomSpace_of_isAlgebraicStack B S hS 𝒴.val 𝒴.property p.base _ _)
    _ (Over.mk (fieldValuedPointBaseMap B S hS a).left) hs hf hc ?_
  intro T u
  have hTeq : (Over.map (fieldValuedPointBaseMap B S hS a).left).obj (Over.mk u.left) = T :=
    congrArg Over.mk (Over.w u)
  have hbij := (bijective_pointAutomorphismSpaceMap_app_iff B S hS f a
    (Opposite.op (Over.mk u.left))).mp
      ((ConcreteCategory.isIso_iff_bijective _).1 (h (Opposite.op (Over.mk u.left))))
  rwa [show (Over.map (fieldValuedPointBaseMap B S hS a).left).op.obj
      (Opposite.op (Over.mk u.left)) = Opposite.op T from congrArg Opposite.op hTeq] at hbij

/-- **Stacks 0DTV.** Let `f : 𝒳 ⟶ 𝒴` be a 1-morphism of algebraic stacks and let `x` be a point
of `|𝒳|`. The map `G_x ⟶ G_y` of automorphism group algebraic spaces, where `y = f ∘ x`, is an
isomorphism for *some* field-valued representative `x : Spec k → 𝒳` of the point if and only if
it is an isomorphism for *every* such representative.

Two representatives of one point admit a common refinement. Over a field extension the map of
automorphism group algebraic spaces is a base change of the map below, and being an isomorphism
is fpqc local on the target (**Stacks 041Y**), so it passes both ways between a representative
and a refinement. -/
@[stacks 0DTV]
theorem exists_isIso_pointAutomorphismSpaceMap_iff_forall (f : 𝒳 ⟶ 𝒴)
    (q : points B S hS 𝒳.val.val 𝒳.val.isFiberedInGroupoids) :
    (∃ p : FieldValuedPoint B S hS 𝒳.val.val,
        pointClass B S hS 𝒳.val.val 𝒳.val.isFiberedInGroupoids p = q ∧
          IsIso (pointAutomorphismSpaceMap B S hS f p)) ↔
      ∀ p : FieldValuedPoint B S hS 𝒳.val.val,
        pointClass B S hS 𝒳.val.val 𝒳.val.isFiberedInGroupoids p = q →
          IsIso (pointAutomorphismSpaceMap B S hS f p) := by
  constructor
  · rintro ⟨p, hp, hPp⟩ r hr
    obtain ⟨t, ⟨fp⟩, ⟨fr⟩⟩ :=
      (class_eq_class_iff_hasCommonExtension B S hS 𝒳.val.val
        𝒳.val.isFiberedInGroupoids p r).mp (hp.trans hr.symm)
    exact isIso_pointAutomorphismSpaceMap_of_hom' B S hS f fr
      (isIso_pointAutomorphismSpaceMap_of_hom B S hS f fp hPp)
  · intro h
    obtain ⟨p, hp⟩ := Quotient.exists_rep q
    exact ⟨p, hp, h p hp⟩

end AutomorphismGroupMap

end AlgebraicGeometry.Stack

end
