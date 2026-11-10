module

public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.PointwiseFibreFullFaithful
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.Quotient.Functoriality
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.Quotient.OpenSubgroupoidQuotientStack
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.Quotient.PresentationFullyFaithful
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.QuotientStackSquares.FunctorialityComparisonFullness

/-!
# Morphisms between presented objects under the 1-morphism of a groupoid morphism

Let `φ : (U, P, s', t', c') ⟶ (U', R, s, t, c)` be a morphism of groupoids in algebraic spaces and
`[φ] : [U/P] ⟶ [U'/R]` the induced 1-morphism of quotient stacks of Stacks 046Q. A point `x` of
the object space `U` over a test object `T` presents an object `π(x)` of `[U/P]` over `T`, and by
Stacks 044V the morphisms of `[U/P]` between presented objects are the arrows of the pointwise
groupoid of `P`. This file records what `[φ]` does to such morphisms: it is the arrow map of `φ`,
conjugated by the 2-isomorphism of Stacks 046Q.

In particular `[φ]` is surjective on the morphisms between two presented objects as soon as every
arrow of `R` between the images of the two points comes from an arrow of `P` between the points
themselves. This is the shape in which the proof of Stacks 0DU5 uses an open subgroupoid
containing every arrow over a given point: the self 2-fibre product of the spectrum of that point
does not see the difference between `[U/P]` and `[U/R]`.

## Main results

* `CategoryTheory.Functor.map_surjective_of_iso_comp`: surjectivity on morphisms transfers along
  a 2-isomorphism `Φ ⋙ F' ≅ F ⋙ M` when `F'` is full.
* `CategoryTheory.Pseudofunctor.CoGrothendieck.map_map_surjective`: the functor of Grothendieck
  constructions induced by a strong transformation is surjective on the morphisms between two
  objects when the components are surjective on the fibre morphisms involved.
* `Deformation.GroupoidInFunctors.Hom.evaluation_map_surjective`: the evaluated functor of a
  morphism of groupoids in functors is surjective on the morphisms between two points when every
  arrow between their images is the image of an arrow between them.
* `AlgebraicGeometry.Stack.quotientStackMap_map_pointwiseToQuotientStack`: on the image of an
  arrow of the pointwise groupoid fibration, `[φ]` is the image of the pointwise map of `φ`,
  conjugated by the 2-isomorphism of Stacks 046Q.
* `AlgebraicGeometry.Stack.quotientStackMap_map_surjective`: `[φ]` is surjective on the morphisms
  between two presented objects when every arrow of `R` between the images of the two points,
  after pulling back along any morphism of test objects, comes from an arrow of `P`.
* `AlgebraicGeometry.Stack.quotientStackFiberHomEquiv`: **Stacks 044V** on fibre morphisms, the
  morphisms over the identity of `T` between two presented objects are the arrows of `R` over `T`
  with the given source and target.

## References

* [Stacks Project, Tag 044V](https://stacks.math.columbia.edu/tag/044V)
* [Stacks Project, Tag 044X](https://stacks.math.columbia.edu/tag/044X)
* [Stacks Project, Tag 046Q](https://stacks.math.columbia.edu/tag/046Q)
* [Stacks Project, Tag 0DU5](https://stacks.math.columbia.edu/tag/0DU5)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Pseudofunctor Opposite

namespace CategoryTheory.Functor

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

/-- **Surjectivity on morphisms transfers along a 2-isomorphism.** Let `α : Φ ⋙ F' ≅ F ⋙ M` and
let `F'` be full. If `Φ` is surjective on the morphisms `a ⟶ b`, then `M` is surjective on the
morphisms `F a ⟶ F b`: a morphism `g : M (F a) ⟶ M (F b)` conjugated by `α` is `F' h'` for some
`h' : Φ a ⟶ Φ b`, which is `Φ h`, and naturality of `α` gives `M (F h) = g`. -/
theorem map_surjective_of_iso_comp {A : Type u₁} [Category.{v₁} A] {A' : Type u₂}
    [Category.{v₂} A'] {X : Type u₃} [Category.{v₃} X] {Y : Type u₄} [Category.{v₄} Y]
    (F : A ⥤ X) (F' : A' ⥤ Y) (Φ : A ⥤ A') (M : X ⥤ Y) (α : Φ ⋙ F' ≅ F ⋙ M) [F'.Full]
    {a b : A} (hΦ : Function.Surjective (Φ.map : (a ⟶ b) → (Φ.obj a ⟶ Φ.obj b))) :
    Function.Surjective (M.map : (F.obj a ⟶ F.obj b) → (M.obj (F.obj a) ⟶ M.obj (F.obj b))) := by
  intro g
  obtain ⟨h', hh'⟩ := F'.map_surjective (α.hom.app a ≫ g ≫ α.inv.app b)
  obtain ⟨h, rfl⟩ := hΦ h'
  refine ⟨F.map h, (NatIso.naturality_1 α h).symm.trans ?_⟩
  rw [Functor.comp_map, hh']
  simp

end CategoryTheory.Functor

namespace CategoryTheory.Pseudofunctor.CoGrothendieck

open scoped CategoryTheory.Pseudofunctor.StrongTrans

universe v₁ u₁ v₂ u₂

/-- **The Grothendieck construction of a strong transformation is surjective on the morphisms
between two objects** as soon as, for every morphism `g` of the base between their bases, the
component of the transformation is surjective on the fibre morphisms from the first fibre object
to the pullback along `g` of the second. The fibre component of the image of `⟨g, f⟩` is `α f`
followed by the invertible naturality constraint, which can be cancelled. -/
theorem map_map_surjective {D : Type u₁} [Category.{v₁} D]
    {P Q : Pseudofunctor (LocallyDiscrete Dᵒᵖ) Cat.{v₂, u₂}} (α : P ⟶ Q) {X Y : ∫ᶜ P}
    (h : ∀ g : X.base ⟶ Y.base, Function.Surjective
      ((α.app ⟨op X.base⟩).toFunctor.map :
        (X.fiber ⟶ (P.map g.op.toLoc).toFunctor.obj Y.fiber) → _)) :
    Function.Surjective ((CoGrothendieck.map α).map : (X ⟶ Y) → _) := by
  rintro ⟨g, f⟩
  obtain ⟨f', hf'⟩ := h g (f ≫ (α.naturality g.op.toLoc).inv.toNatTrans.app Y.fiber)
  refine ⟨⟨g, f'⟩, CoGrothendieck.Hom.ext _ _ rfl ?_⟩
  change (α.app ⟨op X.base⟩).toFunctor.map f' ≫
      (α.naturality g.op.toLoc).hom.toNatTrans.app Y.fiber = f ≫ eqToHom rfl
  rw [hf', eqToHom_refl, Category.comp_id]
  exact (Category.assoc _ _ _).trans ((congrArg (f ≫ ·)
    (Cat.Hom.inv_hom_id_toNatTrans_app (α.naturality g.op.toLoc) Y.fiber)).trans
      (Category.comp_id f))

end CategoryTheory.Pseudofunctor.CoGrothendieck

namespace Deformation.GroupoidInFunctors.Hom

universe u v w

/-- **The evaluated functor of a morphism of groupoids in functors is surjective on the morphisms
between two points** when every arrow between the images of the points is the image of an arrow
between the points. An arrow of an evaluated groupoid is its underlying element of the arrow
functor, and the evaluated functor acts on it by the arrow map. -/
theorem evaluation_map_surjective {C : Type u} [Category.{v} C]
    {G H : GroupoidInFunctors.{u, v, w} C} (F : Hom G H) (T : C) (x y : G.Evaluation T)
    (h : ∀ b : H.arrows.obj T, H.source.app T b = F.mapObjects.app T x →
      H.target.app T b = F.mapObjects.app T y →
        ∃ a : G.arrows.obj T, G.source.app T a = x ∧ G.target.app T a = y ∧
          F.mapArrows.app T a = b) :
    Function.Surjective ((F.evaluation T).map : (x ⟶ y) → _) := by
  intro f
  obtain ⟨a, hs, ht, ha⟩ := h (H.evaluationArrowEquiv T _ _ f).1
    (H.evaluationArrowEquiv T _ _ f).2.1 (H.evaluationArrowEquiv T _ _ f).2.2
  refine ⟨(G.evaluationArrowEquiv T x y).symm ⟨a, hs, ht⟩, ?_⟩
  refine (H.evaluationArrowEquiv T _ _).injective (Subtype.ext ?_)
  rwa [evaluation_map_arrow, Equiv.apply_symm_apply]

end Deformation.GroupoidInFunctors.Hom

namespace AlgebraicGeometry.Stack

universe u

variable {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
  {B : AlgebraicSpaces C S hS}

/-- The 2-isomorphism of Stacks 046Q, read as a natural isomorphism of the underlying functors:
the pointwise map of `φ` followed by the map to `[U'/R]` is isomorphic to the map to `[U/P]`
followed by `[φ]`. Its components lie over identities of the site. -/
noncomputable def quotientStackMapCommutesIso {G H : GroupoidInAlgebraicSpaces C S hS B}
    (φ : GroupoidInAlgebraicSpaces.Hom G H) :
    (quotientPointwiseMap φ).toFunctor ⋙ pointwiseToQuotientStack H ≅
      pointwiseToQuotientStack G ⋙ (quotientStackMap φ).toFunctor :=
  (BasedNatTrans.forgetful _ _).mapIso (quotientStackMap_commutes φ)

/-- **On the image of a pointwise arrow, `[φ]` is the image of the pointwise map of `φ`**,
conjugated by the 2-isomorphism of Stacks 046Q. This is naturality of that 2-isomorphism. -/
theorem quotientStackMap_map_pointwiseToQuotientStack {G H : GroupoidInAlgebraicSpaces C S hS B}
    (φ : GroupoidInAlgebraicSpaces.Hom G H)
    {X Y : (presheafOfGroupoids (evaluationGroupoidFunctor G.toGroupoidInFunctors)).obj}
    (f : X ⟶ Y) :
    (quotientStackMap φ).toFunctor.map ((pointwiseToQuotientStack G).map f) =
      (quotientStackMapCommutesIso φ).inv.app X ≫
        (pointwiseToQuotientStack H).map ((quotientPointwiseMap φ).toFunctor.map f) ≫
          (quotientStackMapCommutesIso φ).hom.app Y := by
  exact (NatIso.naturality_1 (quotientStackMapCommutesIso φ) f).symm

/-- **`[φ]` is surjective on the morphisms between two presented objects** as soon as, for every
morphism `g : T ⟶ T'` of test objects, every arrow of the target groupoid over `T` from the
image of `x` to the image of the pullback of `y` along `g` is the image of an arrow of the source
groupoid from `x` to that pullback.

A morphism of `[U/P]` from `π(x)` to `π(y)`, for `x` over `T` and `y` over `T'`, is by
Stacks 044X the image of a unique arrow of the pointwise groupoid fibration, which is a morphism
`g : T ⟶ T'` together with an arrow of the groupoid of points over `T` from `x` to `g^* y`. -/
theorem quotientStackMap_map_surjective {G H : GroupoidInAlgebraicSpaces C S hS B}
    (φ : GroupoidInAlgebraicSpaces.Hom G H)
    {X Y : (presheafOfGroupoids (evaluationGroupoidFunctor G.toGroupoidInFunctors)).obj}
    (h : ∀ g : X.base ⟶ Y.base, ∀ b : H.arrows.obj.obj (op X.base),
      H.toGroupoidInFunctors.source.app (op X.base) b =
          φ.toGroupoidHom.mapObjects.app (op X.base) X.fiber →
        H.toGroupoidInFunctors.target.app (op X.base) b =
          φ.toGroupoidHom.mapObjects.app (op X.base) (G.objects.obj.map g.op Y.fiber) →
        ∃ a : G.arrows.obj.obj (op X.base),
          G.toGroupoidInFunctors.source.app (op X.base) a = X.fiber ∧
          G.toGroupoidInFunctors.target.app (op X.base) a = G.objects.obj.map g.op Y.fiber ∧
          φ.toGroupoidHom.mapArrows.app (op X.base) a = b) :
    Function.Surjective ((quotientStackMap φ).toFunctor.map :
      ((pointwiseToQuotientStack G).obj X ⟶ (pointwiseToQuotientStack G).obj Y) → _) := by
  have hfull : (pointwiseToQuotientStack H).Full := (fullyFaithfulPointwiseToQuotientStack H).full
  refine Functor.map_surjective_of_iso_comp _ _ _ _ (quotientStackMapCommutesIso φ) ?_
  refine CoGrothendieck.map_map_surjective (quotientPointwiseMapData φ).val ?_
  intro g
  rw [(quotientPointwiseMapData φ).property.1]
  exact φ.toGroupoidHom.evaluation_map_surjective (op X.base) _ _ (h g)

/-- **On fibre morphisms between presented objects, `[φ]` is the evaluated functor of `φ`**,
conjugated by the 2-isomorphism of Stacks 046Q: the image under `[φ]` of the morphism of `[U/P]`
over `T` named by an arrow `r` of the groupoid of points is, up to the two components of that
2-isomorphism, the morphism of `[U'/R]` over `T` named by the image of `r`, whose underlying
element of the arrow space is the image of that of `r` under the arrow map of `φ`
(`Deformation.GroupoidInFunctors.Hom.evaluation_map_arrow`). -/
theorem quotientStackMap_map_pointwiseToQuotientStackFiber
    {G H : GroupoidInAlgebraicSpaces C S hS B}
    (φ : GroupoidInAlgebraicSpaces.Hom G H) (T : BigFppfOver C S hS)
    {x y : G.toGroupoidInFunctors.Evaluation (op T)} (r : x ⟶ y) :
    (quotientStackMap φ).toFunctor.map ((pointwiseToQuotientStackFiber G T).map r).1 =
      (quotientStackMapCommutesIso φ).inv.app ⟨T, x⟩ ≫
        ((pointwiseToQuotientStackFiber H T).map ((φ.toGroupoidHom.evaluation (op T)).map r)).1 ≫
          (quotientStackMapCommutesIso φ).hom.app ⟨T, y⟩ := by
  refine (quotientStackMap_map_pointwiseToQuotientStack φ
    ((CoGrothendieck.ι _ T).map r)).trans ?_
  congr 2
  exact congrArg (pointwiseToQuotientStack H).map (quotientPointwiseMap_map_ι φ T r)

/-- **`[φ]` is bijective on the morphisms between two presented objects** when the arrow map of
`φ` is a monomorphism and the arrow condition of
`AlgebraicGeometry.Stack.quotientStackMap_map_surjective` holds: injectivity is the faithfulness
of `[φ]` (`AlgebraicGeometry.Stack.faithful_quotientStackMap_of_mono`). -/
theorem quotientStackMap_map_bijective {G H : GroupoidInAlgebraicSpaces C S hS B}
    (φ : GroupoidInAlgebraicSpaces.Hom G H) (hmono : Mono φ.toGroupoidHom.mapArrows)
    {X Y : (presheafOfGroupoids (evaluationGroupoidFunctor G.toGroupoidInFunctors)).obj}
    (h : ∀ g : X.base ⟶ Y.base, ∀ b : H.arrows.obj.obj (op X.base),
      H.toGroupoidInFunctors.source.app (op X.base) b =
          φ.toGroupoidHom.mapObjects.app (op X.base) X.fiber →
        H.toGroupoidInFunctors.target.app (op X.base) b =
          φ.toGroupoidHom.mapObjects.app (op X.base) (G.objects.obj.map g.op Y.fiber) →
        ∃ a : G.arrows.obj.obj (op X.base),
          G.toGroupoidInFunctors.source.app (op X.base) a = X.fiber ∧
          G.toGroupoidInFunctors.target.app (op X.base) a = G.objects.obj.map g.op Y.fiber ∧
          φ.toGroupoidHom.mapArrows.app (op X.base) a = b) :
    Function.Bijective ((quotientStackMap φ).toFunctor.map :
      ((pointwiseToQuotientStack G).obj X ⟶ (pointwiseToQuotientStack G).obj Y) → _) := by
  have := faithful_quotientStackMap_of_mono φ hmono
  exact ⟨(quotientStackMap φ).toFunctor.map_injective, quotientStackMap_map_surjective φ h⟩

/-- **Stacks 044V on fibre morphisms.** The morphisms over the identity of `T` between the two
objects of `[U/R]` presented by points `x` and `y` of the object space over `T` are the arrows of
the arrow space over `T` with source `x` and target `y`. The identification is the inverse of the
fully faithful functor of Stacks 044X from the groupoid of points to the fibre, followed by the
description of an arrow of the groupoid of points by its underlying element of the arrow space. -/
noncomputable def quotientStackFiberHomEquiv (G : GroupoidInAlgebraicSpaces C S hS B)
    (T : BigFppfOver C S hS) (x y : G.toGroupoidInFunctors.Evaluation (op T)) :
    ((pointwiseToQuotientStackFiber G T).obj x ⟶ (pointwiseToQuotientStackFiber G T).obj y) ≃
      { a : G.arrows.obj.obj (op T) // G.toGroupoidInFunctors.source.app (op T) a = x ∧
        G.toGroupoidInFunctors.target.app (op T) a = y } :=
  ((fullyFaithful_pointwiseToQuotientStackFiber G T).some.homEquiv).symm.trans
    (G.toGroupoidInFunctors.evaluationArrowEquiv (op T) x y)

/-- The identification of Stacks 044V on fibre morphisms sends the image of an arrow of the
groupoid of points to that arrow's underlying element of the arrow space. -/
theorem quotientStackFiberHomEquiv_map (G : GroupoidInAlgebraicSpaces C S hS B)
    (T : BigFppfOver C S hS) {x y : G.toGroupoidInFunctors.Evaluation (op T)} (f : x ⟶ y) :
    quotientStackFiberHomEquiv G T x y ((pointwiseToQuotientStackFiber G T).map f) =
      G.toGroupoidInFunctors.evaluationArrowEquiv (op T) x y f := by
  change G.toGroupoidInFunctors.evaluationArrowEquiv (op T) x y
      ((fullyFaithful_pointwiseToQuotientStackFiber G T).some.homEquiv.symm
        ((pointwiseToQuotientStackFiber G T).map f)) = _
  congr 1
  exact (fullyFaithful_pointwiseToQuotientStackFiber G T).some.preimage_map f

end AlgebraicGeometry.Stack

end
