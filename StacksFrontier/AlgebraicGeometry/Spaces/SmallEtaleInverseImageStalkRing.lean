module

public import Mathlib.CategoryTheory.Adjunction.Mates
public import Mathlib.CategoryTheory.Sites.Point.Comap
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposRingImageComposition
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.PullbackStalk.ElementsColimit
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleInverseImageStalk
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleRingedToposHom
public import StacksFrontier.CategoryTheory.Sites.Topos.MorphismOfTopoiRing
import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.CommRingPullback

/-!
# Fibres of the inverse image of a sheaf of rings on the small étale site

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S` and let `x` be a geometric
point of `X`, with image `f ∘ x`.  The fibre at `x` of the inverse image along the canonical
morphism of small étale ringed topoi of Stacks 03G8 of a sheaf of commutative rings on the small
étale site of `Y` is the fibre of that sheaf at `f ∘ x`:
```
(f⁻¹ G)_x ≅ G_{f ∘ x},
```
naturally in `G`.  This is the sheaf-of-rings form of Stacks 04K2, part (4), whose form for
sheaves of sets is `AlgebraicGeometry.Space.smallEtaleInverseImageStalkIso`; it is what makes the
structure map of the morphism of ringed topoi comparable, fibre by fibre, with the canonical
homomorphism of étale local rings of Stacks 04NG.

The comparison is not an instance of Mathlib's
`CategoryTheory.GrothendieckTopology.Point.sheafFiberComapIso`: the morphism of topoi of
Stacks 03G8 is not presented by a functor between the two small étale sites, because a morphism
of algebraic spaces does not pull étale scheme charts of the target back to étale charts of the
source.  The route is therefore through the spaces-étale sites of Stacks 03G0, where base change
along an arbitrary morphism of algebraic spaces is available, and the only handle on the direct
image is `AlgebraicGeometry.Space.smallEtaleRingedToposHom_pushforward`, which compares it with
that base change.

## Main definitions

* `AlgebraicGeometry.Space.smallEtaleRingedToposHom_pushforwardRing`: the comparison of
  `AlgebraicGeometry.Space.smallEtaleRingedToposHom_pushforward` for sheaves of commutative
  rings.
* `AlgebraicGeometry.Space.spacesBaseChangeSkyscraperRingIso`: the direct image of sheaves of
  commutative rings along base change carries the spaces-étale skyscraper at `x` to the one at
  `f ∘ x`.
* `AlgebraicGeometry.Space.smallEtaleSkyscraperRingIso`: the direct image of sheaves of
  commutative rings along the morphism of Stacks 03G8 carries the small étale skyscraper at `x`
  to the one at `f ∘ x`.
* `AlgebraicGeometry.Space.smallEtaleInverseImageFiberRingIso`: the fibre comparison this file
  exists for.
* `CategoryTheory.GrothendieckTopology.Point.presheafFiberIsoOfFiberIso` and
  `...sheafFiberIsoOfFiberIso`: the fibre functors of two points of a site with isomorphic fibre
  functors are isomorphic, at any category of coefficients.
* `CategoryTheory.GrothendieckTopology.Point.skyscraperPushforwardIso`: the direct image along a
  continuous functor of sites of the skyscraper at a point of the target site is the skyscraper at
  a point of the source site whose fibre functor it induces, *with its projections computed*
  (`...skyscraperPushforwardIso_hom_app_π`).

## Main results

* `CategoryTheory.GrothendieckTopology.Point.toPresheafFiber_presheafFiberIsoOfFiberIso` and
  `...toPresheafFiber_presheafFiberIsoOfFiberIso_inv`: the comparison of fibre functors induced by
  an isomorphism of fibre functors, on germs.
* `CategoryTheory.GrothendieckTopology.Point.rightAdjointUniq_comap_skyscraper_hom_app_π` and
  `...comapSkyscraperPushforward_hom_app_π`: the projections of the skyscraper comparison
  obtained by *uniqueness of right adjoints* from an isomorphism of fibre functors — the form
  `AlgebraicGeometry.Space.spacesBaseChangeSkyscraperRingIso` takes.  They are the projections of
  the reindexing comparison, so that comparison has a formula on sections too.
* `AlgebraicGeometry.Space.spacesBaseChangeSkyscraperRingIso_hom_app_π`: that formula for the
  base-change comparison itself.
* `AlgebraicGeometry.Space.smallEtaleRingedToposHom_pushforwardRing_forget`: forgetting the ring
  operations in the ring-level direct-image comparison gives back the set-level comparison it was
  built from.  Five of its six factors are the identity on underlying sheaves of sets and the
  sixth is that comparison, transported; the per-factor statements are
  `AlgebraicGeometry.Space.pushforwardRingTail1_forget` and
  `...pushforwardRingTail«i»_forget`.

## Implementation notes

The fibre comparison is the right-adjoint transpose of the skyscraper comparison, so it is the
canonical comparison and not an arbitrary isomorphism of the two functors; that is the reason the
skyscraper statement is proved first and the fibre statement is obtained from it by
`CategoryTheory.conjugateIsoEquiv`.

The skyscraper comparison splices three identifications.  Over the comparison functor of
Stacks 03G1 nothing has to be done: the fibre functor of
`AlgebraicGeometry.Space.etaleSitePoint` is the spaces-étale fibre functor restricted along that
comparison *on the nose*, so the small étale skyscraper is the restriction of the spaces-étale
skyscraper by `CategoryTheory.Iso.refl`.  Over base change the identification is the transpose of
`AlgebraicGeometry.Space.spacesBaseChangeFiberIso`, by uniqueness of right adjoints.  The middle
step is the ring-level form of
`AlgebraicGeometry.Space.smallEtaleRingedToposHom_pushforward`, assembled from
`Stacks.Sheaves.ToposPullback.restrictionCommRingNatIso`,
`...pullbackCommRingSheafFunctorComp` and `...pullbackCommRingSheafFunctorIsoOfNatIso`: each of
the four functors in sight transports the ring operations along its set-level form, so the
set-level comparison transports too.

`Point.presheafFiberIsoOfFiberIso` is
`AlgebraicGeometry.CategoryOfElements.presheafColimIsoOfNatIso` with the coefficients left
arbitrary rather than taken in `Type (u + 1)`, which is what the ring-valued case needs.

## References

* [Stacks Project, Tag 04K2](https://stacks.math.columbia.edu/tag/04K2)
* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8)
* [Stacks Project, Tag 03G1](https://stacks.math.columbia.edu/tag/03G1)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.GrothendieckTopology
open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward

universe w v v' uC uD uA vA u

/-! ### The direct image of a skyscraper, with its projections computed

A skyscraper sheaf is a product of copies of one object indexed by the fibre of a point, and the
direct image along a continuous functor of sites is restriction, so the direct image of a
skyscraper is again such a product — indexed by the fibre functor restricted along the functor of
sites.  An isomorphism of that restricted fibre functor with the fibre functor of a point of the
source site therefore identifies the two skyscrapers *by a reindexing of products*, and every
projection of the resulting isomorphism is a projection.

This is what makes the identification usable in germ computations: the transpose of the same
isomorphism across `CategoryTheory.GrothendieckTopology.Point.skyscraperSheafAdjunction` — which
is how `AlgebraicGeometry.Space.spacesBaseChangeSkyscraperRingIso` obtains it, by uniqueness of
right adjoints — is pinned only up to that uniqueness and has no formula on sections.
-/

namespace CategoryTheory.Limits

variable {A : Type uA} [Category.{vA} A] [HasProducts.{w} A]

/-- Reindexing a product of copies of a single object along a map of index types. -/
noncomputable def piReindex {ι κ : Type w} (p : κ → ι) (M : A) :
    (∏ᶜ fun _ : ι => M) ⟶ (∏ᶜ fun _ : κ => M) :=
  Pi.map' p (fun _ => 𝟙 M)

/-- The `b`-th projection of `piReindex p M` is the `p b`-th projection. -/
@[reassoc (attr := simp)]
theorem piReindex_π {ι κ : Type w} (p : κ → ι) (M : A) (b : κ) :
    piReindex p M ≫ Pi.π (fun _ : κ => M) b = Pi.π (fun _ : ι => M) (p b) :=
  (Pi.map'_comp_π _ _ b).trans (Category.comp_id _)

/-- Reindexing along `p` and then along `q` is reindexing along `p ∘ q`. -/
theorem piReindex_comp {ι κ ν : Type w} (p : κ → ι) (q : ν → κ) (M : A) :
    piReindex p M ≫ piReindex q M = piReindex (p ∘ q) M :=
  Pi.hom_ext _ _ fun c => by rw [Category.assoc, piReindex_π, piReindex_π, piReindex_π]; rfl

/-- Reindexing along the identity is the identity. -/
theorem piReindex_id {ι : Type w} (M : A) : piReindex (id : ι → ι) M = 𝟙 _ :=
  Pi.hom_ext _ _ fun a => by rw [piReindex_π, Category.id_comp]; rfl

/-- The map of products of copies of one object induced by a morphism of that object. -/
noncomputable def piValueMap (ι : Type w) {M N : A} (k : M ⟶ N) :
    (∏ᶜ fun _ : ι => M) ⟶ (∏ᶜ fun _ : ι => N) :=
  Pi.map (β := ι) (f := fun _ => M) (g := fun _ => N) fun _ => k

/-- The `a`-th projection of `piValueMap ι k` is the `a`-th projection followed by `k`. -/
@[reassoc (attr := simp)]
theorem piValueMap_π (ι : Type w) {M N : A} (k : M ⟶ N) (a : ι) :
    piValueMap ι k ≫ Pi.π (fun _ : ι => N) a = Pi.π (fun _ : ι => M) a ≫ k :=
  Pi.map_π _ a

/-- Reindexing commutes with the map of products induced by a morphism `k : M ⟶ N`. -/
@[reassoc]
theorem piReindex_comp_piValueMap {ι κ : Type w} (p : κ → ι) {M N : A} (k : M ⟶ N) :
    piReindex p M ≫ piValueMap κ k = piValueMap ι k ≫ piReindex p N :=
  Pi.hom_ext _ _ fun b => by
    rw [Category.assoc, piValueMap_π, piReindex_π_assoc, Category.assoc, piReindex_π, piValueMap_π]

end CategoryTheory.Limits

namespace CategoryTheory.GrothendieckTopology.Point

variable {C : Type uC} [Category.{v} C] {D : Type uD} [Category.{v'} D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    {A : Type uA} [Category.{vA} A] [HasProducts.{w} A]
    (Φ : Point.{w} K) (Ψ : Point.{w} J) (u : C ⥤ D) [u.IsContinuous J K]
    (e : u ⋙ Φ.fiber ≅ Ψ.fiber)

/-- The underlying presheaves of the direct image of a skyscraper and of the skyscraper at a
point whose fibre functor it induces are both products of copies of the same object, and the
isomorphism of fibre functors reindexes one to the other. -/
def skyscraperPushforwardPresheafIso (M : A) :
    ((u.sheafPushforwardContinuous A J K).obj (Φ.skyscraperSheaf M)).obj ≅
      (Ψ.skyscraperSheaf M).obj where
  hom :=
    { app V := piReindex (fun y => e.inv.app V.unop y) M
      naturality := by
        intro V W g
        change piReindex (fun z => Φ.fiber.map (u.map g.unop) z) M ≫
            piReindex (fun y => e.inv.app W.unop y) M =
          piReindex (fun y => e.inv.app V.unop y) M ≫
            piReindex (fun z => Ψ.fiber.map g.unop z) M
        rw [piReindex_comp, piReindex_comp]
        exact congrArg (fun p => piReindex p M)
          (congrArg (fun k => (ConcreteCategory.hom k : _ → _))
            (e.inv.naturality g.unop)).symm }
  inv :=
    { app V := piReindex (fun y => e.hom.app V.unop y) M
      naturality := by
        intro V W g
        change piReindex (fun z => Ψ.fiber.map g.unop z) M ≫
            piReindex (fun y => e.hom.app W.unop y) M =
          piReindex (fun y => e.hom.app V.unop y) M ≫
            piReindex (fun z => Φ.fiber.map (u.map g.unop) z) M
        rw [piReindex_comp, piReindex_comp]
        exact congrArg (fun p => piReindex p M)
          (congrArg (fun k => (ConcreteCategory.hom k : _ → _))
            (e.hom.naturality g.unop)).symm }
  hom_inv_id := by
    refine NatTrans.ext (funext fun V => ?_)
    change piReindex (fun y => e.inv.app V.unop y) M ≫
        piReindex (fun y => e.hom.app V.unop y) M = 𝟙 _
    rw [piReindex_comp]
    refine Eq.trans (congrArg (fun p => piReindex p M)
      (congrArg (fun k => (ConcreteCategory.hom k : _ → _))
        (NatTrans.congr_app e.hom_inv_id V.unop))) ?_
    exact piReindex_id M
  inv_hom_id := by
    refine NatTrans.ext (funext fun V => ?_)
    change piReindex (fun y => e.hom.app V.unop y) M ≫
        piReindex (fun y => e.inv.app V.unop y) M = 𝟙 _
    rw [piReindex_comp]
    refine Eq.trans (congrArg (fun p => piReindex p M)
      (congrArg (fun k => (ConcreteCategory.hom k : _ → _))
        (NatTrans.congr_app e.inv_hom_id V.unop))) ?_
    exact piReindex_id M

/-- The direct image along a continuous functor of sites of the skyscraper at a point of the
target site is the skyscraper at a point of the source site whose fibre functor the restricted
one is, naturally in the value of the skyscraper. -/
def skyscraperPushforwardIso :
    Φ.skyscraperSheafFunctor (A := A) ⋙ u.sheafPushforwardContinuous A J K ≅
      Ψ.skyscraperSheafFunctor :=
  NatIso.ofComponents
    (fun M => (fullyFaithfulSheafToPresheaf J A).preimageIso
      (skyscraperPushforwardPresheafIso Φ Ψ u e M))
    (by
      intro M N k
      refine (fullyFaithfulSheafToPresheaf J A).map_injective ?_
      rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp,
        Functor.FullyFaithful.preimageIso_hom, Functor.FullyFaithful.preimageIso_hom,
        (fullyFaithfulSheafToPresheaf J A).map_preimage,
        (fullyFaithfulSheafToPresheaf J A).map_preimage]
      refine NatTrans.ext (funext fun V => ?_)
      change piValueMap _ k ≫ piReindex (fun y => e.inv.app V.unop y) N =
        piReindex (fun y => e.inv.app V.unop y) M ≫ piValueMap _ k
      exact (piReindex_comp_piValueMap _ k).symm)

/-- Every projection of the skyscraper comparison is a projection: the component at a lift `y`
of the point of the source site is the component at the lift of the point of the target site
that the isomorphism of fibre functors assigns to it.  This is the formula on sections that the
right-adjoint transpose of the same comparison does not have. -/
theorem skyscraperPushforwardIso_hom_app_π (M : A) (V : C) (y : Ψ.fiber.obj V) :
    ((sheafToPresheaf J A).map ((skyscraperPushforwardIso Φ Ψ u e).hom.app M)).app
          (Opposite.op V) ≫ Pi.π (fun _ : Ψ.fiber.obj V => M) y =
      Pi.π (fun _ : Φ.fiber.obj (u.obj V) => M) (e.inv.app V y) := by
  have h : (sheafToPresheaf J A).map ((skyscraperPushforwardIso Φ Ψ u e).hom.app M) =
      (skyscraperPushforwardPresheafIso Φ Ψ u e M).hom :=
    (fullyFaithfulSheafToPresheaf J A).map_preimage _
  rw [h]
  exact piReindex_π _ M y

/-- **The transpose skyscraper comparison on sections.**  The comparison of the direct image of
the skyscraper at a point of the target site with the skyscraper at a point of the source site,
*obtained by uniqueness of right adjoints* from the induced comparison of fibre functors, has the
same projections as the reindexing comparison
`CategoryTheory.GrothendieckTopology.Point.skyscraperPushforwardIso`: the component at a lift `y`
of the point of the source site is the component at the lift the isomorphism of fibre functors
assigns to it.

This is what gives the comparison used by
`AlgebraicGeometry.Space.spacesBaseChangeSkyscraperRingIso` a formula on sections.  The right
adjoint of the fibre functor of a point is the skyscraper functor, so a map into a skyscraper is
determined by its transpose
(`CategoryTheory.GrothendieckTopology.Point.skyscraperPresheafHomEquiv_app_π`); the transpose of
this one is the counit of the composite adjunction, which evaluates a germ at its own index. -/
theorem rightAdjointUniq_comap_skyscraper_hom_app_π [HasColimitsOfSize.{w, w} A]
    (Φ : Point.{w} K) (Ψ : Point.{w} J) (u : C ⥤ D) [u.IsContinuous J K] [RepresentablyFlat u]
    (hcover : CoverPreserving J K u) (e : u ⋙ Φ.fiber ≅ Ψ.fiber)
    [InitiallySmall.{w} (u ⋙ Φ.fiber).Elements] (M : A) (V : C) (y : Ψ.fiber.obj V) :
    ((Adjunction.rightAdjointUniq
          ((Φ.comap u hcover).skyscraperSheafAdjunction.ofNatIsoLeft
            (sheafFiberIsoOfFiberIso (Φ.comap u hcover) Ψ e))
          Ψ.skyscraperSheafAdjunction).hom.app M).hom.app (Opposite.op V) ≫
        Pi.π (fun _ : Ψ.fiber.obj V => M) y =
      Pi.π (fun _ : Φ.fiber.obj (u.obj V) => M) (e.inv.app V y) := by
  set adjc := (Φ.comap u hcover).skyscraperSheafAdjunction (A := A) with hadjc
  set eB := sheafFiberIsoOfFiberIso (Φ.comap u hcover) Ψ e (A := A) with heB
  set adj1 := adjc.ofNatIsoLeft eB with hadj1
  set S := (Φ.comap u hcover).skyscraperSheafFunctor.obj M with hS
  have h1 : (Adjunction.rightAdjointUniq adj1 Ψ.skyscraperSheafAdjunction).hom.app M =
      Ψ.skyscraperSheafAdjunction.homEquiv _ M (adj1.counit.app M) := by
    rw [← Adjunction.homEquiv_symm_rightAdjointUniq_hom_app adj1
      Ψ.skyscraperSheafAdjunction M, Equiv.apply_symm_apply]
  have key : ((Ψ.skyscraperSheafAdjunction.homEquiv S M) (adj1.counit.app M)).hom =
      Ψ.skyscraperPresheafHomEquiv (adj1.counit.app M) :=
    Ψ.skyscraperSheafAdjunction_homEquiv_apply_hom _
  rw [h1, key]
  have hc : adj1.counit.app M = eB.inv.app S ≫ adjc.counit.app M := rfl
  have h3 : Ψ.toPresheafFiber V y S.obj ≫ eB.inv.app S =
      (Φ.comap u hcover).toPresheafFiber V (e.inv.app V y) S.obj :=
    toPresheafFiber_presheafFiberIsoOfFiberIso_inv (Φ.comap u hcover) Ψ e S.obj V y
  have h4 : adjc.counit.app M = (Φ.comap u hcover).skyscraperPresheafHomEquiv.symm
      (𝟙 ((Φ.comap u hcover).skyscraperPresheaf M)) := rfl
  refine Eq.trans (Ψ.skyscraperPresheafHomEquiv_app_π (P := S.obj) (M := M)
    (adj1.counit.app M) V y) ?_
  refine Eq.trans (congrArg (fun t => Ψ.toPresheafFiber V y S.obj ≫ t) hc) ?_
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  refine Eq.trans (congrArg (fun t => t ≫ adjc.counit.app M) h3) ?_
  refine Eq.trans (congrArg
    (fun t => (Φ.comap u hcover).toPresheafFiber V (e.inv.app V y) S.obj ≫ t) h4) ?_
  refine Eq.trans ((Φ.comap u hcover).toPresheafFiber_skyscraperPresheafHomEquiv_symm
    (𝟙 ((Φ.comap u hcover).skyscraperPresheaf M)) V (e.inv.app V y)) ?_
  exact Category.id_comp _

/-- **The whole base-change skyscraper comparison on sections.**  Splicing Mathlib's
identification of the direct image of a skyscraper along a continuous functor with the
skyscraper of the comapped point — which is `CategoryTheory.Iso.refl` — with the transpose
comparison of `...rightAdjointUniq_comap_skyscraper_hom_app_π` gives a comparison whose
projections are projections.

This is the shape `AlgebraicGeometry.Space.spacesBaseChangeSkyscraperRingIso` has, so it
computes that comparison on sections. -/
theorem comapSkyscraperPushforward_hom_app_π [HasColimitsOfSize.{w, w} A]
    (Φ : Point.{w} K) (Ψ : Point.{w} J) (u : C ⥤ D) [u.IsContinuous J K] [RepresentablyFlat u]
    (hcover : CoverPreserving J K u) (e : u ⋙ Φ.fiber ≅ Ψ.fiber)
    [InitiallySmall.{w} (u ⋙ Φ.fiber).Elements] (M : A) (V : C) (y : Ψ.fiber.obj V) :
    ((Φ.skyscraperSheafFunctorCompSheafPushforwardContinuous u hcover A ≪≫
          Adjunction.rightAdjointUniq
            ((Φ.comap u hcover).skyscraperSheafAdjunction.ofNatIsoLeft
              (sheafFiberIsoOfFiberIso (Φ.comap u hcover) Ψ e))
            Ψ.skyscraperSheafAdjunction).hom.app M).hom.app (Opposite.op V) ≫
        Pi.π (fun _ : Ψ.fiber.obj V => M) y =
      Pi.π (fun _ : Φ.fiber.obj (u.obj V) => M) (e.inv.app V y) := by
  have h : (Φ.skyscraperSheafFunctorCompSheafPushforwardContinuous u hcover A ≪≫
        Adjunction.rightAdjointUniq
          ((Φ.comap u hcover).skyscraperSheafAdjunction.ofNatIsoLeft
            (sheafFiberIsoOfFiberIso (Φ.comap u hcover) Ψ e))
          Ψ.skyscraperSheafAdjunction).hom.app M =
      𝟙 _ ≫ (Adjunction.rightAdjointUniq
          ((Φ.comap u hcover).skyscraperSheafAdjunction.ofNatIsoLeft
            (sheafFiberIsoOfFiberIso (Φ.comap u hcover) Ψ e))
          Ψ.skyscraperSheafAdjunction).hom.app M := rfl
  rw [h, Category.id_comp]
  exact rightAdjointUniq_comap_skyscraper_hom_app_π Φ Ψ u hcover e M V y

end CategoryTheory.GrothendieckTopology.Point

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)

/-! ### The ring-level direct-image comparison, factor by factor

The comparison below is a chain of six isomorphisms, and its content on underlying sheaves of
sets is that five of them are the identity there and the sixth is the set-level comparison.
Reading that off the chain means splitting `(sheafCompose _ (forget CommRingCat)).map` across a
composite, and `CategoryTheory.Functor.map_comp` splits a six-fold composite only once: the goal
is not type-correct at `implicit` transparency, so the abstraction needed for the remaining
splits cannot be formed.  The chain is therefore built as nested *two*-factor composites, each
with its own `_forget` lemma, which is the shape
`AlgebraicGeometry.Space.smallEtaleRingedToposHom_representableRing_forget` already handles.
-/

/-- A functor sends a composite to `e` if it sends the factors to `c` and `d` with `c ≫ d = e`. -/
private theorem map_comp_eq_of_eq {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {X Y Z : C} {a : X ⟶ Y} {b : Y ⟶ Z} {c : F.obj X ⟶ F.obj Y} {d : F.obj Y ⟶ F.obj Z}
    {e : F.obj X ⟶ F.obj Z} (ha : F.map a = c) (hb : F.map b = d) (h : c ≫ d = e) :
    F.map (a ≫ b) = e := by
  rw [F.map_comp, ha, hb, h]

section PushforwardRingFactors

variable [(spacesBaseChange B S hS f).functor.IsContinuous
    (SpacesEtale.topology B S hS Y) (SpacesEtale.topology B S hS X)]

/-- The last factor of the ring-level direct-image comparison: restriction along the comparison
functor of `Y`, transported to sheaves of commutative rings, *is* restriction of sheaves of
commutative rings. -/
def pushforwardRingTail6 :
    (spacesBaseChange B S hS f).functor.sheafPushforwardContinuous CommRingCat.{u}
          (SpacesEtale.topology B S hS Y) (SpacesEtale.topology B S hS X) ⋙
        pullbackCommRingSheafFunctor.{u, u, u, u + 1, u + 1, u + 1}
          (SmallEtale.topology B S hS Y.1)
          ((comparisonFunctor B S hS Y).sheafPushforwardContinuous (Type u)
            (SmallEtale.topology B S hS Y.1) (SpacesEtale.topology B S hS Y)) ≅
      (spacesBaseChange B S hS f).functor.sheafPushforwardContinuous CommRingCat.{u}
          (SpacesEtale.topology B S hS Y) (SpacesEtale.topology B S hS X) ⋙
        (comparisonFunctor B S hS Y).sheafPushforwardContinuous CommRingCat.{u}
          (SmallEtale.topology B S hS Y.1) (SpacesEtale.topology B S hS Y) :=
  Functor.isoWhiskerLeft _
    (restrictionCommRingNatIso.{u}
      (SmallEtale.topology B S hS Y.1) (SpacesEtale.topology B S hS Y)
      (comparisonFunctor B S hS Y))

/-- The last two factors. -/
def pushforwardRingTail5 :
    pullbackCommRingSheafFunctor.{u, u, u + 1, u + 1, u + 1, u + 1}
          (SpacesEtale.topology B S hS Y)
          ((spacesBaseChange B S hS f).functor.sheafPushforwardContinuous (Type u)
            (SpacesEtale.topology B S hS Y) (SpacesEtale.topology B S hS X)) ⋙
        pullbackCommRingSheafFunctor.{u, u, u, u + 1, u + 1, u + 1}
          (SmallEtale.topology B S hS Y.1)
          ((comparisonFunctor B S hS Y).sheafPushforwardContinuous (Type u)
            (SmallEtale.topology B S hS Y.1) (SpacesEtale.topology B S hS Y)) ≅
      (spacesBaseChange B S hS f).functor.sheafPushforwardContinuous CommRingCat.{u}
          (SpacesEtale.topology B S hS Y) (SpacesEtale.topology B S hS X) ⋙
        (comparisonFunctor B S hS Y).sheafPushforwardContinuous CommRingCat.{u}
          (SmallEtale.topology B S hS Y.1) (SpacesEtale.topology B S hS Y) :=
  Functor.isoWhiskerRight
      (restrictionCommRingNatIso.{u}
        (SpacesEtale.topology B S hS Y) (SpacesEtale.topology B S hS X)
        (spacesBaseChange B S hS f).functor) _ ≪≫
    pushforwardRingTail6 B S hS f

/-- The last three factors. -/
def pushforwardRingTail4 :
    pullbackCommRingSheafFunctor.{u, u, u, u + 1, u + 1, u + 1}
        (SmallEtale.topology B S hS Y.1)
        ((spacesBaseChange B S hS f).functor.sheafPushforwardContinuous (Type u)
            (SpacesEtale.topology B S hS Y) (SpacesEtale.topology B S hS X) ⋙
          (comparisonFunctor B S hS Y).sheafPushforwardContinuous (Type u)
            (SmallEtale.topology B S hS Y.1) (SpacesEtale.topology B S hS Y)) ≅
      (spacesBaseChange B S hS f).functor.sheafPushforwardContinuous CommRingCat.{u}
          (SpacesEtale.topology B S hS Y) (SpacesEtale.topology B S hS X) ⋙
        (comparisonFunctor B S hS Y).sheafPushforwardContinuous CommRingCat.{u}
          (SmallEtale.topology B S hS Y.1) (SpacesEtale.topology B S hS Y) :=
  (pullbackCommRingSheafFunctorComp.{u}
      (SpacesEtale.topology B S hS Y) (SmallEtale.topology B S hS Y.1)
      ((spacesBaseChange B S hS f).functor.sheafPushforwardContinuous (Type u)
        (SpacesEtale.topology B S hS Y) (SpacesEtale.topology B S hS X))
      ((comparisonFunctor B S hS Y).sheafPushforwardContinuous (Type u)
        (SmallEtale.topology B S hS Y.1) (SpacesEtale.topology B S hS Y))).symm ≪≫
    pushforwardRingTail5 B S hS f

/-- The last four factors; the first of them is the set-level comparison, transported. -/
def pushforwardRingTail3 :
    pullbackCommRingSheafFunctor.{u, u, u, u + 1, u + 1, u + 1}
        (SmallEtale.topology B S hS Y.1)
        ((comparisonFunctor B S hS X).sheafPushforwardContinuous (Type u)
            (SmallEtale.topology B S hS X.1) (SpacesEtale.topology B S hS X) ⋙
          (smallEtaleRingedToposHom B S hS f).toToposHom.pushforward) ≅
      (spacesBaseChange B S hS f).functor.sheafPushforwardContinuous CommRingCat.{u}
          (SpacesEtale.topology B S hS Y) (SpacesEtale.topology B S hS X) ⋙
        (comparisonFunctor B S hS Y).sheafPushforwardContinuous CommRingCat.{u}
          (SmallEtale.topology B S hS Y.1) (SpacesEtale.topology B S hS Y) :=
  pullbackCommRingSheafFunctorIsoOfNatIso.{u, u, u, u + 1, u + 1, u + 1} _
      (smallEtaleRingedToposHom_pushforward B S hS f) ≪≫
    pushforwardRingTail4 B S hS f

/-- The last five factors. -/
def pushforwardRingTail2 :
    pullbackCommRingSheafFunctor.{u, u, u, u + 1, u + 1, u + 1}
          (SmallEtale.topology B S hS X.1)
          ((comparisonFunctor B S hS X).sheafPushforwardContinuous (Type u)
            (SmallEtale.topology B S hS X.1) (SpacesEtale.topology B S hS X)) ⋙
        (smallEtaleRingedToposHom B S hS f).toToposHom.pushforwardRing ≅
      (spacesBaseChange B S hS f).functor.sheafPushforwardContinuous CommRingCat.{u}
          (SpacesEtale.topology B S hS Y) (SpacesEtale.topology B S hS X) ⋙
        (comparisonFunctor B S hS Y).sheafPushforwardContinuous CommRingCat.{u}
          (SmallEtale.topology B S hS Y.1) (SpacesEtale.topology B S hS Y) :=
  pullbackCommRingSheafFunctorComp.{u}
      (SmallEtale.topology B S hS X.1) (SmallEtale.topology B S hS Y.1)
      ((comparisonFunctor B S hS X).sheafPushforwardContinuous (Type u)
        (SmallEtale.topology B S hS X.1) (SpacesEtale.topology B S hS X))
      (smallEtaleRingedToposHom B S hS f).toToposHom.pushforward ≪≫
    pushforwardRingTail3 B S hS f

/-- On underlying sheaves of sets the last factor is the identity. -/
theorem pushforwardRingTail6_forget
    (H : Sheaf (SpacesEtale.topology B S hS X) CommRingCat.{u}) :
    (sheafCompose (SmallEtale.topology B S hS Y.1) (forget CommRingCat.{u})).map
        ((pushforwardRingTail6 B S hS f).hom.app H) = 𝟙 _ :=
  underlyingRingSheaf_map_restrictionCommRingNatIso_hom.{u}
    (SmallEtale.topology B S hS Y.1) (SpacesEtale.topology B S hS Y)
    (comparisonFunctor B S hS Y) _

/-- The fifth factor is the identity on underlying sheaves of sets: it is restriction along the
comparison functor of `Y` of a comparison that is already the identity there. -/
private theorem pushforwardRingFactor5_forget
    (H : Sheaf (SpacesEtale.topology B S hS X) CommRingCat.{u}) :
    (sheafCompose (SmallEtale.topology B S hS Y.1) (forget CommRingCat.{u})).map
        ((Functor.isoWhiskerRight
            (restrictionCommRingNatIso.{u} (SpacesEtale.topology B S hS Y)
              (SpacesEtale.topology B S hS X) (spacesBaseChange B S hS f).functor)
            (pullbackCommRingSheafFunctor.{u, u, u, u + 1, u + 1, u + 1}
              (SmallEtale.topology B S hS Y.1)
              ((comparisonFunctor B S hS Y).sheafPushforwardContinuous (Type u)
                (SmallEtale.topology B S hS Y.1)
                (SpacesEtale.topology B S hS Y)))).hom.app H) = 𝟙 _ := by
  change (sheafCompose (SmallEtale.topology B S hS Y.1) (forget CommRingCat.{u})).map
      (pullbackCommRingSheafMap.{u, u, u, u + 1, u + 1, u + 1}
        (SmallEtale.topology B S hS Y.1)
        ((comparisonFunctor B S hS Y).sheafPushforwardContinuous (Type u)
          (SmallEtale.topology B S hS Y.1) (SpacesEtale.topology B S hS Y))
        ((restrictionCommRingNatIso.{u} (SpacesEtale.topology B S hS Y)
          (SpacesEtale.topology B S hS X)
          (spacesBaseChange B S hS f).functor).hom.app H)) = 𝟙 _
  rw [underlyingRingSheaf_map_pullbackCommRingSheafMap.{u, u, u, u + 1, u + 1, u + 1},
    underlyingRingSheaf_map_restrictionCommRingNatIso_hom]
  exact CategoryTheory.Functor.map_id _ _

/-- The fourth factor is the identity on underlying sheaves of sets: it is the inverse of a
comparison of iterated inverse images, and that comparison is the identity there. -/
private theorem pushforwardRingFactor4_forget
    (H : Sheaf (SpacesEtale.topology B S hS X) CommRingCat.{u}) :
    (sheafCompose (SmallEtale.topology B S hS Y.1) (forget CommRingCat.{u})).map
        ((pullbackCommRingSheafFunctorComp.{u, u + 1, u + 1, u + 1, u + 1, u, u + 1}
            (SpacesEtale.topology B S hS Y) (SmallEtale.topology B S hS Y.1)
            ((spacesBaseChange B S hS f).functor.sheafPushforwardContinuous (Type u)
              (SpacesEtale.topology B S hS Y) (SpacesEtale.topology B S hS X))
            ((comparisonFunctor B S hS Y).sheafPushforwardContinuous (Type u)
              (SmallEtale.topology B S hS Y.1)
              (SpacesEtale.topology B S hS Y))).inv.app H) = 𝟙 _ := by
  rw [← Iso.app_inv, ← Functor.mapIso_inv]
  exact Iso.inv_ext ((Category.comp_id _).trans
    (forget_map_pullbackCommRingSheafComp_hom.{u, u + 1, u + 1, u + 1, u + 1, u, u + 1}
      (SpacesEtale.topology B S hS Y) (SmallEtale.topology B S hS Y.1)
      ((spacesBaseChange B S hS f).functor.sheafPushforwardContinuous (Type u)
        (SpacesEtale.topology B S hS Y) (SpacesEtale.topology B S hS X))
      ((comparisonFunctor B S hS Y).sheafPushforwardContinuous (Type u)
        (SmallEtale.topology B S hS Y.1) (SpacesEtale.topology B S hS Y)) H))

omit [(spacesBaseChange B S hS f).functor.IsContinuous
  (SpacesEtale.topology B S hS Y) (SpacesEtale.topology B S hS X)] in
/-- The second factor is the identity on underlying sheaves of sets. -/
private theorem pushforwardRingFactor2_forget
    (H : Sheaf (SpacesEtale.topology B S hS X) CommRingCat.{u}) :
    (sheafCompose (SmallEtale.topology B S hS Y.1) (forget CommRingCat.{u})).map
        ((pullbackCommRingSheafFunctorComp.{u, u + 1, u + 1, u, u + 1, u, u + 1}
            (SmallEtale.topology B S hS X.1) (SmallEtale.topology B S hS Y.1)
            ((comparisonFunctor B S hS X).sheafPushforwardContinuous (Type u)
              (SmallEtale.topology B S hS X.1) (SpacesEtale.topology B S hS X))
            (smallEtaleRingedToposHom B S hS f).toToposHom.pushforward).hom.app H) = 𝟙 _ :=
  forget_map_pullbackCommRingSheafComp_hom.{u, u + 1, u + 1, u, u + 1, u, u + 1}
    (SmallEtale.topology B S hS X.1) (SmallEtale.topology B S hS Y.1)
    ((comparisonFunctor B S hS X).sheafPushforwardContinuous (Type u)
      (SmallEtale.topology B S hS X.1) (SpacesEtale.topology B S hS X))
    (smallEtaleRingedToposHom B S hS f).toToposHom.pushforward H

/-- On underlying sheaves of sets the last two factors are the identity. -/
theorem pushforwardRingTail5_forget
    (H : Sheaf (SpacesEtale.topology B S hS X) CommRingCat.{u}) :
    (sheafCompose (SmallEtale.topology B S hS Y.1) (forget CommRingCat.{u})).map
        ((pushforwardRingTail5 B S hS f).hom.app H) = 𝟙 _ := by
  exact map_comp_eq_of_eq _ (pushforwardRingFactor5_forget B S hS f H)
    (pushforwardRingTail6_forget B S hS f H) (Category.comp_id _)

/-- On underlying sheaves of sets the last three factors are the identity. -/
theorem pushforwardRingTail4_forget
    (H : Sheaf (SpacesEtale.topology B S hS X) CommRingCat.{u}) :
    (sheafCompose (SmallEtale.topology B S hS Y.1) (forget CommRingCat.{u})).map
        ((pushforwardRingTail4 B S hS f).hom.app H) = 𝟙 _ := by
  exact map_comp_eq_of_eq _ (pushforwardRingFactor4_forget B S hS f H)
    (pushforwardRingTail5_forget B S hS f H) (Category.comp_id _)

/-- On underlying sheaves of sets the last four factors are the set-level comparison. -/
theorem pushforwardRingTail3_forget
    (H : Sheaf (SpacesEtale.topology B S hS X) CommRingCat.{u}) :
    (sheafCompose (SmallEtale.topology B S hS Y.1) (forget CommRingCat.{u})).map
        ((pushforwardRingTail3 B S hS f).hom.app H) =
      (smallEtaleRingedToposHom_pushforward B S hS f).hom.app
        (Stacks.underlyingRingSheaf (SpacesEtale.topology B S hS X) H) := by
  exact map_comp_eq_of_eq _
    (underlyingRingSheaf_map_pullbackCommRingSheafFunctorIsoOfNatIso_hom.{u, u, u, u + 1,
      u + 1, u + 1} (SmallEtale.topology B S hS Y.1) H
      (smallEtaleRingedToposHom_pushforward B S hS f))
    (pushforwardRingTail4_forget B S hS f H) (Category.comp_id _)

/-- On underlying sheaves of sets the last five factors are the set-level comparison. -/
theorem pushforwardRingTail2_forget
    (H : Sheaf (SpacesEtale.topology B S hS X) CommRingCat.{u}) :
    (sheafCompose (SmallEtale.topology B S hS Y.1) (forget CommRingCat.{u})).map
        ((pushforwardRingTail2 B S hS f).hom.app H) =
      (smallEtaleRingedToposHom_pushforward B S hS f).hom.app
        (Stacks.underlyingRingSheaf (SpacesEtale.topology B S hS X) H) := by
  exact map_comp_eq_of_eq _ (pushforwardRingFactor2_forget B S hS f H)
    (pushforwardRingTail3_forget B S hS f H) (Category.id_comp _)

end PushforwardRingFactors

/-- The first two factors of the ring-level direct-image comparison, grouped.

They are grouped because the straddle their `_forget` statements would otherwise create cannot be
composed: the first factor converts restriction along the comparison functor of `X` into an
inverse image of sheaves of commutative rings *underneath* the direct image, so the middle object
of `factor₁ ≫ factor₂` is two `Stacks.Sheaves.ToposPullback.pullbackCommRingSheaf` layers deep,
and identifying it with either endpoint's set-level form exhausts the elaborator.  Grouped, both
endpoints of the pair are one layer deep and reduce cheaply to the same sheaf of sets. -/
def pushforwardRingTail1 :
    (comparisonFunctor B S hS X).sheafPushforwardContinuous CommRingCat.{u}
          (SmallEtale.topology B S hS X.1) (SpacesEtale.topology B S hS X) ⋙
        (smallEtaleRingedToposHom B S hS f).toToposHom.pushforwardRing ≅
      pullbackCommRingSheafFunctor.{u, u, u, u + 1, u + 1, u + 1}
        (SmallEtale.topology B S hS Y.1)
        ((comparisonFunctor B S hS X).sheafPushforwardContinuous (Type u)
            (SmallEtale.topology B S hS X.1) (SpacesEtale.topology B S hS X) ⋙
          (smallEtaleRingedToposHom B S hS f).toToposHom.pushforward) :=
  Functor.isoWhiskerRight
      (restrictionCommRingNatIso.{u}
        (SmallEtale.topology B S hS X.1) (SpacesEtale.topology B S hS X)
        (comparisonFunctor B S hS X)).symm _ ≪≫
    pullbackCommRingSheafFunctorComp.{u}
      (SmallEtale.topology B S hS X.1) (SmallEtale.topology B S hS Y.1)
      ((comparisonFunctor B S hS X).sheafPushforwardContinuous (Type u)
        (SmallEtale.topology B S hS X.1) (SpacesEtale.topology B S hS X))
      (smallEtaleRingedToposHom B S hS f).toToposHom.pushforward

/-- **Stacks 03G8 for sheaves of commutative rings.** Restriction to the small étale site
followed by the direct image of sheaves of commutative rings along the canonical morphism of
small étale ringed topoi agrees with base change on the spaces-étale sites followed by
restriction on the target.  This is
`AlgebraicGeometry.Space.smallEtaleRingedToposHom_pushforward` with the ring operations carried
along: each of the four functors transports them from its set-level form. -/
def smallEtaleRingedToposHom_pushforwardRing :
    letI := (spacesBaseChange_isMorphismOfSites B S hS f).isContinuous
    (comparisonFunctor B S hS X).sheafPushforwardContinuous CommRingCat.{u}
        (SmallEtale.topology B S hS X.1) (SpacesEtale.topology B S hS X) ⋙
      (smallEtaleRingedToposHom B S hS f).toToposHom.pushforwardRing ≅
    (spacesBaseChange B S hS f).functor.sheafPushforwardContinuous CommRingCat.{u}
        (SpacesEtale.topology B S hS Y) (SpacesEtale.topology B S hS X) ⋙
      (comparisonFunctor B S hS Y).sheafPushforwardContinuous CommRingCat.{u}
        (SmallEtale.topology B S hS Y.1) (SpacesEtale.topology B S hS Y) := by
  letI := (spacesBaseChange_isMorphismOfSites B S hS f).isContinuous
  exact pushforwardRingTail1 B S hS f ≪≫ pushforwardRingTail3 B S hS f

/-- The first factor is the identity on underlying sheaves of sets: it is the direct image of a
comparison that is already the identity there.

The right-hand side is written at the set level — `𝟙` of the restriction of the underlying sheaf
of sets — rather than as `𝟙 _`.  The two ring-level endpoints of the comparison are only
definitionally equal, through `Stacks.Sheaves.ToposPullback.pullbackCommRingSheaf` against
restriction, and asking the elaborator to identify them exhausts its budget. -/
private theorem pushforwardRingFactor1_forget
    (H : Sheaf (SpacesEtale.topology B S hS X) CommRingCat.{u}) :
    (sheafCompose (SmallEtale.topology B S hS Y.1) (forget CommRingCat.{u})).map
        ((Functor.isoWhiskerRight
            (restrictionCommRingNatIso.{u} (SmallEtale.topology B S hS X.1)
              (SpacesEtale.topology B S hS X) (comparisonFunctor B S hS X)).symm
            (smallEtaleRingedToposHom B S hS f).toToposHom.pushforwardRing).hom.app H) =
      𝟙 ((smallEtaleRingedToposHom B S hS f).toToposHom.pushforward.obj
        (((comparisonFunctor B S hS X).sheafPushforwardContinuous (Type u)
            (SmallEtale.topology B S hS X.1) (SpacesEtale.topology B S hS X)).obj
          (Stacks.underlyingRingSheaf (SpacesEtale.topology B S hS X) H))) := by
  have h1 : (sheafCompose (SmallEtale.topology B S hS X.1) (forget CommRingCat.{u})).map
        ((restrictionCommRingNatIso.{u} (SmallEtale.topology B S hS X.1)
          (SpacesEtale.topology B S hS X) (comparisonFunctor B S hS X)).inv.app H) =
      𝟙 (((comparisonFunctor B S hS X).sheafPushforwardContinuous (Type u)
          (SmallEtale.topology B S hS X.1) (SpacesEtale.topology B S hS X)).obj
        (Stacks.underlyingRingSheaf (SpacesEtale.topology B S hS X) H)) :=
    restrictionCommRingIso_inv_forget.{u} (SmallEtale.topology B S hS X.1)
      (SpacesEtale.topology B S hS X) (comparisonFunctor B S hS X) H
  change (sheafCompose (SmallEtale.topology B S hS Y.1) (forget CommRingCat.{u})).map
      ((smallEtaleRingedToposHom B S hS f).toToposHom.pushforwardRing.map
        ((restrictionCommRingNatIso.{u} (SmallEtale.topology B S hS X.1)
          (SpacesEtale.topology B S hS X) (comparisonFunctor B S hS X)).inv.app H)) = _
  refine Eq.trans (MorphismOfTopoi.pushforwardRing_map_forget _ _) ?_
  rw [h1]
  exact CategoryTheory.Functor.map_id _ _

/-- On underlying sheaves of sets the first two factors, grouped, are the identity. -/
theorem pushforwardRingTail1_forget
    (H : Sheaf (SpacesEtale.topology B S hS X) CommRingCat.{u}) :
    (sheafCompose (SmallEtale.topology B S hS Y.1) (forget CommRingCat.{u})).map
        ((pushforwardRingTail1 B S hS f).hom.app H) = 𝟙 _ := by
  exact map_comp_eq_of_eq _ (pushforwardRingFactor1_forget B S hS f H)
    (pushforwardRingFactor2_forget B S hS f H) (Category.comp_id _)

/-- **The ring-level direct-image comparison on underlying sheaves of sets.**  Forgetting the
ring operations in `AlgebraicGeometry.Space.smallEtaleRingedToposHom_pushforwardRing` gives back
the set-level comparison `AlgebraicGeometry.Space.smallEtaleRingedToposHom_pushforward` it was
built from: of its six factors, five are the identity on underlying sheaves of sets and the sixth
is that comparison, transported.

This is what lets the sections formula for the set-level comparison — ultimately
`AlgebraicGeometry.Space.ranChartCone_π_pushforward_comparison` — be applied to the ring-level
one. -/
theorem smallEtaleRingedToposHom_pushforwardRing_forget
    (H : Sheaf (SpacesEtale.topology B S hS X) CommRingCat.{u}) :
    letI := (spacesBaseChange_isMorphismOfSites B S hS f).isContinuous
    (sheafCompose (SmallEtale.topology B S hS Y.1) (forget CommRingCat.{u})).map
        ((smallEtaleRingedToposHom_pushforwardRing B S hS f).hom.app H) =
      (smallEtaleRingedToposHom_pushforward B S hS f).hom.app
        (Stacks.underlyingRingSheaf (SpacesEtale.topology B S hS X) H) := by
  exact map_comp_eq_of_eq _ (pushforwardRingTail1_forget B S hS f H)
    (pushforwardRingTail3_forget B S hS f H) (Category.id_comp _)

variable (x : GeometricPoint B S hS X.1)

/-- The small étale skyscraper at a geometric point is the restriction along the comparison
functor of Stacks 03G1 of the spaces-étale skyscraper at the same point.  Nothing is to be
proved: the fibre functor of `AlgebraicGeometry.Space.etaleSitePoint` is the spaces-étale fibre
functor restricted along the comparison, so the two skyscrapers are the same functor. -/
def chartSkyscraperRingIso :
    (etaleSitePoint B S hS X.1 x X.2).skyscraperSheafFunctor (A := CommRingCat.{u}) ≅
      (spacesEtaleSitePoint x).skyscraperSheafFunctor ⋙
        (comparisonFunctor B S hS X).sheafPushforwardContinuous CommRingCat.{u}
          (SmallEtale.topology B S hS X.1) (SpacesEtale.topology B S hS X) :=
  Iso.refl _

/-- The direct image of sheaves of commutative rings along base change of algebraic spaces étale
over the target carries the spaces-étale skyscraper at a geometric point `x` of the source to the
spaces-étale skyscraper at the image point.  It is the transpose of
`AlgebraicGeometry.Space.spacesBaseChangeFiberIso`, by uniqueness of right adjoints. -/
def spacesBaseChangeSkyscraperRingIso :
    letI := (spacesBaseChange_isMorphismOfSites B S hS f).isContinuous
    (spacesEtaleSitePoint x).skyscraperSheafFunctor (A := CommRingCat.{u}) ⋙
        (spacesBaseChange B S hS f).functor.sheafPushforwardContinuous CommRingCat.{u}
          (SpacesEtale.topology B S hS Y) (SpacesEtale.topology B S hS X) ≅
      (spacesEtaleSitePoint (geometricPointMap f.hom x)).skyscraperSheafFunctor := by
  letI := (spacesBaseChange_isMorphismOfSites B S hS f).isContinuous
  set u := (spacesBaseChange B S hS f).functor with hu
  set Px := spacesEtaleSitePoint x with hPx
  set Py := spacesEtaleSitePoint (geometricPointMap f.hom x) with hPy
  haveI : PreservesLimitsOfShape (Discrete PEmpty.{1}) u :=
    Functor.preservesLimitsOfShape_pempty_of_isTerminal u
      (SpacesEtale.isTerminal_idObj B S hS Y)
      (isTerminal_spacesBaseChange_idObj B S hS f)
  letI : HasFiniteLimits (SpacesEtale B S hS Y) := hasFiniteLimits_of_hasTerminal_and_pullbacks
  letI : PreservesFiniteLimits u := preservesFiniteLimits_of_preservesTerminal_and_pullbacks u
  letI : RepresentablyFlat u := flat_of_preservesFiniteLimits u
  let hcover : CoverPreserving (SpacesEtale.topology B S hS Y)
      (SpacesEtale.topology B S hS X) u := CoverPreserving.of_isContinuous u _ _
  let efib : u ⋙ Px.fiber ≅ Py.fiber := spacesBaseChangeFiberIso B S hS f x
  haveI : InitiallySmall.{u} (u ⋙ Px.fiber).Elements :=
    initiallySmall_of_initial_of_initiallySmall
      (CategoryOfElements.equivalenceOfNatIso efib).inverse
  exact Px.skyscraperSheafFunctorCompSheafPushforwardContinuous u hcover CommRingCat.{u} ≪≫
    Adjunction.rightAdjointUniq
      ((Px.comap u hcover).skyscraperSheafAdjunction.ofNatIsoLeft
        (Point.sheafFiberIsoOfFiberIso (Px.comap u hcover) Py efib))
      Py.skyscraperSheafAdjunction

/-- The direct image of sheaves of commutative rings along the canonical morphism of small étale
ringed topoi of Stacks 03G8 carries the small étale skyscraper at a geometric point `x` of the
source to the small étale skyscraper at the image point. -/
def smallEtaleSkyscraperRingIso :
    (etaleSitePoint B S hS X.1 x X.2).skyscraperSheafFunctor (A := CommRingCat.{u}) ⋙
        (smallEtaleRingedToposHom B S hS f).toToposHom.pushforwardRing ≅
      (etaleSitePoint B S hS Y.1 (geometricPointMap f.hom x) Y.2).skyscraperSheafFunctor := by
  letI := (spacesBaseChange_isMorphismOfSites B S hS f).isContinuous
  exact Functor.isoWhiskerRight (chartSkyscraperRingIso B S hS x) _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (smallEtaleRingedToposHom_pushforwardRing B S hS f) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (spacesBaseChangeSkyscraperRingIso B S hS f x) _ ≪≫
    (chartSkyscraperRingIso B S hS (geometricPointMap f.hom x)).symm

/-- **Stacks 04K2, part (4), for sheaves of commutative rings.** The fibre at a geometric point
`x` of `X` of the inverse image along the canonical morphism of small étale ringed topoi of
Stacks 03G8 of a sheaf of commutative rings on the small étale site of `Y` is the fibre of that
sheaf at the image point `f ∘ x`, naturally in the sheaf.

It is the right-adjoint transpose of
`AlgebraicGeometry.Space.smallEtaleSkyscraperRingIso`, so it is the canonical comparison. -/
def smallEtaleInverseImageFiberRingIso :
    (etaleSitePoint B S hS Y.1 (geometricPointMap f.hom x) Y.2).sheafFiber
        (A := CommRingCat.{u}) ≅
      (smallEtaleRingedToposHom B S hS f).toToposHom.inverseImageRing ⋙
        (etaleSitePoint B S hS X.1 x X.2).sheafFiber (A := CommRingCat.{u}) :=
  (conjugateIsoEquiv
      ((smallEtaleRingedToposHom B S hS f).toToposHom.ringAdjunction.comp
        (etaleSitePoint B S hS X.1 x X.2).skyscraperSheafAdjunction)
      (etaleSitePoint B S hS Y.1 (geometricPointMap f.hom x) Y.2).skyscraperSheafAdjunction).symm
    (smallEtaleSkyscraperRingIso B S hS f x)

/-- **The base-change skyscraper comparison on sections.**  Over an algebraic space `V` étale
over `Y` and at a lift `v` of the image point `f ∘ x`, the component of
`AlgebraicGeometry.Space.spacesBaseChangeSkyscraperRingIso` is the projection to the lift of `x`
into `X ×_Y V` that the cartesian square of Stacks 03G2, part (1) assigns to `v`.

Although the comparison is obtained by uniqueness of right adjoints, and so is pinned only by
that uniqueness, its projections are projections:
`CategoryTheory.GrothendieckTopology.Point.comapSkyscraperPushforward_hom_app_π`. -/
theorem spacesBaseChangeSkyscraperRingIso_hom_app_π (M : CommRingCat.{u})
    (V : SpacesEtale B S hS Y)
    (v : (spacesEtaleSitePoint (geometricPointMap f.hom x)).fiber.obj V) :
    letI := (spacesBaseChange_isMorphismOfSites B S hS f).isContinuous
    ((spacesBaseChangeSkyscraperRingIso B S hS f x).hom.app M).hom.app (Opposite.op V) ≫
        Pi.π (fun _ : (spacesEtaleSitePoint (geometricPointMap f.hom x)).fiber.obj V => M) v =
      Pi.π (fun _ : (spacesEtaleSitePoint x).fiber.obj
        ((spacesBaseChange B S hS f).functor.obj V) => M)
        ((spacesBaseChangeFiberIso B S hS f x).inv.app V v) := by
  have := (spacesBaseChange_isMorphismOfSites B S hS f).isContinuous
  have : PreservesLimitsOfShape (Discrete PEmpty.{1}) (spacesBaseChange B S hS f).functor :=
    Functor.preservesLimitsOfShape_pempty_of_isTerminal _
      (SpacesEtale.isTerminal_idObj B S hS Y)
      (isTerminal_spacesBaseChange_idObj B S hS f)
  have : HasFiniteLimits (SpacesEtale B S hS Y) := hasFiniteLimits_of_hasTerminal_and_pullbacks
  have : PreservesFiniteLimits (spacesBaseChange B S hS f).functor :=
    preservesFiniteLimits_of_preservesTerminal_and_pullbacks _
  have : RepresentablyFlat (spacesBaseChange B S hS f).functor :=
    flat_of_preservesFiniteLimits _
  let efib : (spacesBaseChange B S hS f).functor ⋙ (spacesEtaleSitePoint x).fiber ≅
      (spacesEtaleSitePoint (geometricPointMap f.hom x)).fiber :=
    spacesBaseChangeFiberIso B S hS f x
  have : InitiallySmall.{u}
      ((spacesBaseChange B S hS f).functor ⋙ (spacesEtaleSitePoint x).fiber).Elements :=
    initiallySmall_of_initial_of_initiallySmall
      (CategoryOfElements.equivalenceOfNatIso efib).inverse
  exact Point.comapSkyscraperPushforward_hom_app_π (spacesEtaleSitePoint x)
    (spacesEtaleSitePoint (geometricPointMap f.hom x)) (spacesBaseChange B S hS f).functor
    (CoverPreserving.of_isContinuous _ _ _) (spacesBaseChangeFiberIso B S hS f x) M V v

end AlgebraicGeometry.Space

end
