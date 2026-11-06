module

public import StacksFrontier.Deformation.Artin.Basic
public import StacksFrontier.Deformation.Artin.Infinitesimal.AutomorphismFunctor
public import StacksFrontier.Deformation.Artin.Infinitesimal.TangentFunctor
public import StacksFrontier.Deformation.Artin.RimSchlessinger
public import StacksFrontier.Deformation.Artin.TangentSpace
public import StacksFrontier.Deformation.PredeformationTangent.TangentVectorSpace
public import StacksFrontier.Deformation.Artin.DeformationObjectExt
public import StacksFrontier.AlgebraicGeometry.Topologies.FppfPostInclusion
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Comparison of the two deformation spaces of a field-valued point

Let `𝒳` be a category fibred in groupoids over the big fppf site of a locally Noetherian
scheme `S` satisfying the Rim–Schlessinger condition (RS*), let `k` be a field of finite type
over `S`, and let `x₀` be an object of `𝒳` over `Spec k`. There are then two descriptions of
the first-order infinitesimal data of `x₀`.

On one side stands the deformation category `𝓕_{𝒳,k,x₀}` over the category `𝒞_Λ` of Artinian
local algebras: condition (RS*) makes it a deformation category, its functor of fibrewise
isomorphism classes satisfies Schlessinger's condition (S2), and its value on the dual numbers
is therefore a `k`-vector space. On the other side stands the tangent functor `T_{x₀}` of
`𝒳` itself, whose value on a vector space `V` is the set of isomorphism classes of lifts of
`x₀` along the square-zero immersion `Spec k ⟶ Spec k[V]`. This file identifies the two,
linearly and compatibly with the two descriptions of a first-order deformation.

## Main results

* `Deformation.Artin.tangentSpace_deformationCategory_linearEquiv` — the tangent space of the
  deformation category is the value of the tangent functor at the rank-one vector space,
  by a `k`-linear equivalence carrying the class of a deformation to the class of the
  corresponding lift.
* `Deformation.Artin.infinitesimalAutomorphisms_deformationCategory_linearEquiv` — the
  infinitesimal automorphisms of the deformation category are the value of the infinitesimal
  automorphism functor at the rank-one vector space, by a `k`-linear equivalence carrying an
  automorphism to the endomorphism of the trivial deformation with the same arrow.
* `Deformation.Artin.exists_deformationClassEquiv_squareZeroLiftClasses`,
  `Deformation.Artin.exists_trivialDeformationFunctor_infinitesimalAutomorphisms` — the two
  translations underlying these, which use neither (RS*) nor the tangent functors.

## Implementation notes

The source gives no proof: the statement is an unwinding of the two constructions, and that
unwinding is what this file carries out. A deformation of `x₀` over `k[V]` is an arrow out of
`x₀` whose image is the closed point of `Spec k[V]`, and a lift of `x₀` along the square-zero
immersion is the same arrow read in the fibre of `CategoryTheory.Under.post`; the translation
between the two presentations, in both directions and on arrows as well as objects, gives a
bijection of isomorphism classes for every finite-dimensional `V`, natural in `V`.

For the infinitesimal automorphisms the same translation applies to arrows rather than to
objects: an automorphism of a deformation over `k[\epsilon]` is an automorphism of the
corresponding lift of `x_0`, and the dual-number deformation is the trivial one because it is
a pushforward of the point. The `k`-vector space structure on `Inf(F_{X,k,x_0})` is
transported along that bijection and pinned by it, the comparison being the identity on
arrows of `X`.

Both vector-space structures come from the unique `k`-linear lift of a finite-product
preserving set-valued functor on finite-dimensional vector spaces,
`Deformation.linearFunctorLift_unique` (Tag 06I6). That uniqueness is what makes the
comparison forced rather than chosen: a natural isomorphism of the two set-valued functors
lifts to a natural transformation of their linear lifts (Tag 06I7), whose components are
therefore linear, and the comparison is the component at the rank-one vector space.

## References

* [Stacks Project, Tag 0D18](https://stacks.math.columbia.edu/tag/0D18)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

/- The goals below mention fibres of structure functors and the induced functor on under
categories; those are built from definitions that the `implicit` transparency level does not
unfold, so naming the unfolding chain here is what makes the goals type-correct at that
level. -/
attribute [local implicit_reducible] CategoryTheory.Functor.Fiber
  CategoryTheory.Functor.Fiber.fiberInclusion
  CategoryTheory.BasedCategory.ofFunctor
  Deformation.Artin.predeformationCategory

universe u v w

namespace Deformation.Artin

-- Four facts about the big fppf site and slice categories stood here as `private`
-- re-declarations. Each now goes to the declaration that already stated it:
-- objects of a strictly full subcategory, to Mathlib's
-- `CategoryTheory.ObjectProperty.FullSubcategory.ext` (generated by `@[ext]`, the second field
-- being a proposition); the structure map of a slice equality, to the Mathlib composite
-- `Over.w`/`Over.eqToHom_left`, inlined at its one remaining use; and injectivity of
-- `Over.post B.inclusion` on objects and on morphisms, to
-- `AlgebraicGeometry.BigFppfOver.obj_injective_post_inclusion` and
-- `AlgebraicGeometry.BigFppfOver.map_injective_post_inclusion`, public in
-- `StacksFrontier.AlgebraicGeometry.Topologies.FppfPostInclusion` (closure 23).

/-- The cardinality of a finite power is bounded by the field's own size bound. -/
private theorem mk_fun_le (K : Type u) (n : ℕ) :
    Cardinal.mk (Fin n → K) ≤ max Cardinal.aleph0 (Cardinal.mk K) := by
  induction n with
  | zero =>
    have h : Cardinal.mk (Fin 0 → K) = 1 := Cardinal.mk_eq_one _
    rw [h]
    exact le_trans Cardinal.one_le_aleph0 (le_max_left _ _)
  | succ n ih =>
    rw [Cardinal.mk_congr (Fin.succFunEquiv K n), Cardinal.mk_prod, Cardinal.lift_id,
      Cardinal.lift_id]
    refine le_trans (Cardinal.mul_le_max _ _) ?_
    exact max_le (max_le ih (le_max_right _ _)) (le_max_left _ _)

/-- A finite-dimensional vector space is no bigger than the field it is defined over. -/
private theorem mk_fgModule_le {K : Type u} [Field K] (V : FGModuleCat.{u} K) :
    Cardinal.mk (V : Type u) ≤ max Cardinal.aleph0 (Cardinal.mk K) := by
  have : Module.Finite K (V : Type u) := V.property
  let b := Module.finBasis K (V : Type u)
  rw [Cardinal.mk_congr b.equivFun.toEquiv]
  exact mk_fun_le K _

section Setup

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
  (hk : B.Contains (Spec (.of k)))

include hk in
/-- Every finite-dimensional vector space over `k` is a site module: its trivial square-zero
extension is no bigger than `k` itself. -/
public theorem isFG_le_isSiteModule : ModuleCat.isFG.{u} k ≤ IsSiteModule k B := by
  intro M hM
  have : Module.Finite k (M : Type u) := hM
  have hk' : max Cardinal.aleph0 (Cardinal.mk k) < B.cutoff := by
    have h : (Spec (.of k)).size < B.cutoff := hk
    rwa [Scheme.size_Spec] at h
  have hmk : Cardinal.mk (squareZeroRing k M) < B.cutoff := by
    show Cardinal.mk (k × (M : Type u)) < B.cutoff
    rw [Cardinal.mk_prod, Cardinal.lift_id, Cardinal.lift_id]
    refine lt_of_le_of_lt (Cardinal.mul_le_max _ _) ?_
    refine max_lt (max_lt (lt_of_le_of_lt (le_max_right _ _) hk') ?_) B.aleph0_lt_cutoff
    exact lt_of_le_of_lt (mk_fgModule_le (⟨M, hM⟩ : FGModuleCat.{u} k)) hk'
  simpa [IsSiteModule, Scheme.size_Spec] using ⟨B.aleph0_lt_cutoff, hmk⟩

/-- The finite-dimensional vector spaces, read as site modules. -/
public def fgSiteModule : FGModuleCat.{u} k ⥤ SiteModule k B :=
  ObjectProperty.ιOfLE (isFG_le_isSiteModule B hk)

/-- The residue map of the trivial square-zero extension of `k` by `V` is the first
projection. -/
private theorem residueMap_artinianSquareZero (V : FGModuleCat.{u} k) :
    residueMap ((artinianSquareZeroExtensionFunctor Λ k).obj V) =
      (TrivSqZeroExt.fstHom k k V.obj).toRingHom := by
  apply RingHom.ext
  intro a
  rfl

end Setup

section SiteModuleLinear

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
  (hk : B.Contains (Spec (.of k)))

/-- Reading a finite-dimensional vector space as a site module is an additive operation. -/
private instance fgSiteModule_additive : (fgSiteModule B hk).Additive where
  map_add := rfl

/-- Reading a finite-dimensional vector space as a site module is `k`-linear. -/
private instance fgSiteModule_linear : (fgSiteModule B hk).Linear k where
  map_smul := by intros; rfl

end SiteModuleLinear

section Translation

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
  (iΛ : Spec (.of Λ) ⟶ S) (toS : Spec (.of k) ⟶ S) (hk : B.Contains (Spec (.of k)))

/-- Two structure maps with the same domain presenting the same slice object agree. -/
private theorem over_mk_hom_eq {C : Type*} [Category C] {W Y : C} {f g : Y ⟶ W}
    (h : (Over.mk f : Over W) = Over.mk g) : f = g := by
  have h2 := (Over.w (eqToHom h)).symm.trans (by rw [Over.eqToHom_left])
  rw [eqToHom_refl] at h2
  simpa using h2

variable {X : Type v} [Category.{w} X] (p : X ⥤ BigFppfOver B S hS) (x₀ : X)
  (hx₀ : (p ⋙ Over.post B.inclusion).obj x₀ =
    Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
  (hx : p.obj x₀ = algebraOver k B S hS toS hk)

include hx₀ hx in
/-- The structure map of the field-valued point factors through the chosen base. -/
private theorem toS_eq : toS = Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ := by
  have h := hx₀.symm.trans (congrArg (Over.post B.inclusion).obj hx)
  have hAlg : (Over.post B.inclusion).obj (algebraOver k B S hS toS hk) =
      (Over.mk toS : Over S) := rfl
  rw [hAlg] at h
  exact (over_mk_hom_eq h).symm

end Translation

section Core

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
  (iΛ : Spec (.of Λ) ⟶ S) (toS : Spec (.of k) ⟶ S) (hk : B.Contains (Spec (.of k)))
  {X : Type v} [Category.{w} X] (p : X ⥤ BigFppfOver B S hS) (x₀ : X)
  (hx₀ : (p ⋙ Over.post B.inclusion).obj x₀ =
    Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
  (hx : p.obj x₀ = algebraOver k B S hS toS hk)

/-- The structure map of the trivial square-zero extension of `k` by `V` factors the
structure map of `k`. -/
private theorem algebraMap_squareZero (V : FGModuleCat.{u} k) :
    CommRingCat.ofHom (algebraMap Λ ((artinianSquareZeroExtensionFunctor Λ k).obj V)) =
      CommRingCat.ofHom (algebraMap Λ k) ≫
        CommRingCat.ofHom (TrivSqZeroExt.inlHom k V.obj) := by
  apply CommRingCat.hom_ext
  ext a
  rfl

/-- On spectra, the structure map of `k[V]` factors through `Spec k`. -/
private theorem specMap_algebraMap_squareZero (V : FGModuleCat.{u} k) :
    Spec.map (CommRingCat.ofHom
        (algebraMap Λ ((artinianSquareZeroExtensionFunctor Λ k).obj V))) =
      Spec.map (CommRingCat.ofHom (TrivSqZeroExt.inlHom k V.obj)) ≫
        Spec.map (CommRingCat.ofHom (algebraMap Λ k)) := by
  rw [← Spec.map_comp]
  exact congrArg Spec.map (algebraMap_squareZero (Λ := Λ) V)

include hx₀ hx in
/-- The site object `Spec k[V]`, read over `S`, is the spectrum of the corresponding object
of `𝒞_Λ`. -/
private theorem squareZeroOver_post (V : FGModuleCat.{u} k) :
    (Over.post B.inclusion).obj
        (squareZeroOver k B S hS toS ((fgSiteModule B hk).obj V)) =
      Over.mk (Spec.map (CommRingCat.ofHom
        (algebraMap Λ ((artinianSquareZeroExtensionFunctor Λ k).obj V))) ≫ iΛ) := by
  have h : (Spec.map (CommRingCat.ofHom (TrivSqZeroExt.inlHom k V.obj)) ≫ toS) =
      Spec.map (CommRingCat.ofHom
        (algebraMap Λ ((artinianSquareZeroExtensionFunctor Λ k).obj V))) ≫ iΛ := by
    rw [toS_eq B S hS iΛ toS hk p x₀ hx₀ hx, specMap_algebraMap_squareZero (Λ := Λ) V]
    exact (Category.assoc _ _ _).symm
  exact congrArg
    (fun g : Spec (CommRingCat.of (TrivSqZeroExt k V.obj)) ⟶ S => (Over.mk g : Over S)) h

variable {A : ArtinianLocalAlgCat.{u, u, u} Λ k}

/-- The base of a deformation is the spectrum of its Artinian local algebra. -/
private theorem deformationObject_base
    (d : DeformationObject iΛ (p ⋙ Over.post B.inclusion) x₀ hx₀) (hd : d.algebra = A) :
    (p ⋙ Over.post B.inclusion).obj d.point =
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ A)) ≫ iΛ) := by
  subst hd; exact d.base

/-- The arrow of a deformation lies over the closed point of the spectrum of its algebra. -/
private theorem deformationObject_arrow_base
    (d : DeformationObject iΛ (p ⋙ Over.post B.inclusion) x₀ hx₀) (hd : d.algebra = A)
    (hb : (p ⋙ Over.post B.inclusion).obj d.point =
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ A)) ≫ iΛ)) :
    eqToHom (congrArg Over.left hx₀).symm ≫
      ((p ⋙ Over.post B.inclusion).map d.arrow).left ≫
        eqToHom (congrArg Over.left hb) =
      Spec.map (CommRingCat.ofHom (residueMap A)) := by
  subst hd; exact d.arrow_base

end Core

section Lift

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
  (iΛ : Spec (.of Λ) ⟶ S) (toS : Spec (.of k) ⟶ S) (hk : B.Contains (Spec (.of k)))
  {X : Type v} [Category.{w} X] (p : X ⥤ BigFppfOver B S hS) (x₀ : X)
  (hx₀ : (p ⋙ Over.post B.inclusion).obj x₀ =
    Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
  (hx : p.obj x₀ = algebraOver k B S hS toS hk)

include hx₀ hx in
/-- The object a deformation over `k[V]` deforms to lies over the site object `Spec k[V]`. -/
private theorem deformation_point_site (V : FGModuleCat.{u} k)
    (d : DeformationObject iΛ (p ⋙ Over.post B.inclusion) x₀ hx₀)
    (hd : d.algebra = (artinianSquareZeroExtensionFunctor Λ k).obj V) :
    p.obj d.point = squareZeroOver k B S hS toS ((fgSiteModule B hk).obj V) := by
  refine BigFppfOver.obj_injective_post_inclusion B S hS ?_
  rw [squareZeroOver_post B S hS iΛ toS hk p x₀ hx₀ hx V]
  exact deformationObject_base B S hS iΛ p x₀ hx₀ d hd

include hx₀ hx in
/-- The arrow of a deformation over `k[V]` lies over the square-zero immersion. -/
private theorem deformation_arrow_isHomLift (V : FGModuleCat.{u} k)
    (d : DeformationObject iΛ (p ⋙ Over.post B.inclusion) x₀ hx₀)
    (hd : d.algebra = (artinianSquareZeroExtensionFunctor Λ k).obj V) :
    p.IsHomLift (squareZeroArrow k B S hS toS hk ((fgSiteModule B hk).obj V)) d.arrow := by
  have hb := deformationObject_base B S hS iΛ p x₀ hx₀ d hd
  have hab := deformationObject_arrow_base B S hS iΛ p x₀ hx₀ d hd hb
  have key := (eqToHom_comp_iff _ _ _).1 hab
  refine IsHomLift.of_commsq p _ d.arrow hx
    (deformation_point_site B S hS iΛ toS hk p x₀ hx₀ hx V d hd) ?_
  apply BigFppfOver.map_injective_post_inclusion B S hS
  rw [Functor.map_comp, Functor.map_comp, eqToHom_map, eqToHom_map]
  apply Over.OverMorphism.ext
  simp only [Over.comp_left, Over.eqToHom_left]
  exact key

/-- The abbreviation for the fibre of lifts of the point along the square-zero immersion
attached to a finite-dimensional vector space. -/
private abbrev liftFiber (V : FGModuleCat.{u} k) :=
  (Under.post p).Fiber (Under.mk (eqToHom hx ≫
    squareZeroArrow k B S hS toS hk ((fgSiteModule B hk).obj V)))

include hx₀ hx in
/-- The arrow of a deformation over `k[V]` presents it as a lift of the point along the
square-zero immersion. -/
private theorem toLiftObj_fiber (V : FGModuleCat.{u} k)
    (d : DeformationObject iΛ (p ⋙ Over.post B.inclusion) x₀ hx₀)
    (hd : d.algebra = (artinianSquareZeroExtensionFunctor Λ k).obj V) :
    (Under.post p).obj (Under.mk d.arrow) =
      Under.mk (eqToHom hx ≫
        squareZeroArrow k B S hS toS hk ((fgSiteModule B hk).obj V)) := by
  have hl := deformation_arrow_isHomLift B S hS iΛ toS hk p x₀ hx₀ hx V d hd
  apply StructuredArrow.obj_ext _ _
    (deformation_point_site B S hS iΛ toS hk p x₀ hx₀ hx V d hd)
  show p.map d.arrow ≫
    eqToHom (deformation_point_site B S hS iΛ toS hk p x₀ hx₀ hx V d hd) =
      eqToHom hx ≫ squareZeroArrow k B S hS toS hk ((fgSiteModule B hk).obj V)
  rw [IsHomLift.fac' p (squareZeroArrow k B S hS toS hk ((fgSiteModule B hk).obj V))
    d.arrow]
  simp

include hx₀ hx in
/-- A deformation over `k[V]`, read as a lift of the point along the square-zero
immersion. -/
@[implicit_reducible]
private def toLiftObj (V : FGModuleCat.{u} k)
    (d : DeformationObject iΛ (p ⋙ Over.post B.inclusion) x₀ hx₀)
    (hd : d.algebra = (artinianSquareZeroExtensionFunctor Λ k).obj V) :
    liftFiber B S hS toS hk p x₀ hx V :=
  ⟨Under.mk d.arrow, toLiftObj_fiber B S hS iΛ toS hk p x₀ hx₀ hx V d hd⟩

/-- The object a lift lives on lies over the site object `Spec k[V]`. -/
private theorem liftFiber_obj (V : FGModuleCat.{u} k)
    (y : liftFiber B S hS toS hk p x₀ hx V) :
    p.obj y.1.right = squareZeroOver k B S hS toS ((fgSiteModule B hk).obj V) :=
  congrArg Under.right y.2

/-- The arrow of a lift commutes with the square-zero immersion. -/
private theorem liftFiber_comm (V : FGModuleCat.{u} k)
    (y : liftFiber B S hS toS hk p x₀ hx V) :
    p.map y.1.hom ≫ eqToHom (liftFiber_obj B S hS toS hk p x₀ hx V y) =
      eqToHom hx ≫ squareZeroArrow k B S hS toS hk ((fgSiteModule B hk).obj V) := by
  have hw := Under.w (eqToHom y.2)
  simp only [Under.eqToHom_right] at hw
  exact hw

/-- The arrow of a lift lies over the square-zero immersion. -/
private theorem liftFiber_isHomLift (V : FGModuleCat.{u} k)
    (y : liftFiber B S hS toS hk p x₀ hx V) :
    p.IsHomLift (squareZeroArrow k B S hS toS hk ((fgSiteModule B hk).obj V)) y.1.hom :=
  IsHomLift.of_commsq p _ y.1.hom hx (liftFiber_obj B S hS toS hk p x₀ hx V y)
    (liftFiber_comm B S hS toS hk p x₀ hx V y)

include hx₀ hx in
/-- The object a lift lives on is the spectrum of the corresponding object of `𝒞_Λ`. -/
private theorem lift_base (V : FGModuleCat.{u} k)
    (y : liftFiber B S hS toS hk p x₀ hx V) :
    (p ⋙ Over.post B.inclusion).obj y.1.right =
      Over.mk (Spec.map (CommRingCat.ofHom
        (algebraMap Λ ((artinianSquareZeroExtensionFunctor Λ k).obj V))) ≫ iΛ) := by
  rw [← squareZeroOver_post B S hS iΛ toS hk p x₀ hx₀ hx V]
  exact congrArg (Over.post B.inclusion).obj (liftFiber_obj B S hS toS hk p x₀ hx V y)

include hx₀ hx in
/-- The arrow of a lift lies over the closed point of the spectrum of `k[V]`. -/
private theorem lift_arrow_base (V : FGModuleCat.{u} k)
    (y : liftFiber B S hS toS hk p x₀ hx V)
    (hb : (p ⋙ Over.post B.inclusion).obj y.1.right =
      Over.mk (Spec.map (CommRingCat.ofHom
        (algebraMap Λ ((artinianSquareZeroExtensionFunctor Λ k).obj V))) ≫ iΛ)) :
    eqToHom (congrArg Over.left hx₀).symm ≫
      ((p ⋙ Over.post B.inclusion).map y.1.hom).left ≫
        eqToHom (congrArg Over.left hb) =
      Spec.map (CommRingCat.ofHom
        (residueMap ((artinianSquareZeroExtensionFunctor Λ k).obj V))) := by
  have hw2 := congrArg (fun t => ((Over.post B.inclusion).map t).left)
    (liftFiber_comm B S hS toS hk p x₀ hx V y)
  simp only [Functor.map_comp, Over.comp_left, Over.eqToHom_left, eqToHom_map] at hw2
  exact (eqToHom_comp_iff _ _ _).2 hw2

include hx₀ hx in
/-- A lift of the point along the square-zero immersion, read as a deformation over
`k[V]`. -/
@[implicit_reducible]
private def fromLiftObj (V : FGModuleCat.{u} k)
    (y : liftFiber B S hS toS hk p x₀ hx V) :
    DeformationObject iΛ (p ⋙ Over.post B.inclusion) x₀ hx₀ where
  algebra := (artinianSquareZeroExtensionFunctor Λ k).obj V
  point := y.1.right
  arrow := y.1.hom
  base := lift_base B S hS iΛ toS hk p x₀ hx₀ hx V y
  arrow_base := lift_arrow_base B S hS iΛ toS hk p x₀ hx₀ hx V y
    (lift_base B S hS iΛ toS hk p x₀ hx₀ hx V y)

/-- The comparison isomorphism of spectra attached to an equality of objects of `𝒞_Λ`. -/
private theorem specMap_ofHom_eqToHom {A A' : ArtinianLocalAlgCat.{u, u, u} Λ k}
    (h : A = A') :
    Spec.map (CommRingCat.ofHom (eqToHom h : A ⟶ A').hom.toRingHom) =
      eqToHom (congrArg
        (fun T : ArtinianLocalAlgCat.{u, u, u} Λ k => Spec (CommRingCat.of T)) h).symm := by
  subst h
  have h1 : (eqToHom (rfl : A = A) : A ⟶ A).hom.toRingHom = RingHom.id A := rfl
  rw [h1]
  simp

/-- A morphism of the big fppf site whose underlying morphism of schemes is a comparison
isomorphism is itself that comparison. -/
private theorem hom_eq_eqToHom {Y Z : BigFppfOver B S hS} (g : Y ⟶ Z) (h : Y = Z)
    (hl : ((Over.post B.inclusion).map g).left =
      eqToHom (congrArg Over.left (congrArg (Over.post B.inclusion).obj h))) :
    g = eqToHom h := by
  apply BigFppfOver.map_injective_post_inclusion B S hS
  rw [eqToHom_map]
  exact Over.OverMorphism.ext (hl.trans (Over.eqToHom_left _).symm)

-- Deformations agree as soon as their algebra, deformed object and arrow agree:
-- `Deformation.Artin.deformationObject_ext`, public in
-- `StacksFrontier.Deformation.Artin.DeformationObjectExt`. A `private` re-declaration stood here,
-- specialised to `q = p ⋙ Over.post B.inclusion`.

include hx₀ hx in
/-- Reading a deformation as a lift and back recovers the deformation. -/
private theorem fromLiftObj_toLiftObj (V : FGModuleCat.{u} k)
    (d : DeformationObject iΛ (p ⋙ Over.post B.inclusion) x₀ hx₀)
    (hd : d.algebra = (artinianSquareZeroExtensionFunctor Λ k).obj V) :
    fromLiftObj B S hS iΛ toS hk p x₀ hx₀ hx V
      (toLiftObj B S hS iΛ toS hk p x₀ hx₀ hx V d hd) = d :=
  deformationObject_ext hd.symm rfl HEq.rfl

include hx₀ hx in
/-- Reading a lift as a deformation and back recovers the lift. -/
private theorem toLiftObj_fromLiftObj (V : FGModuleCat.{u} k)
    (y : liftFiber B S hS toS hk p x₀ hx V) :
    toLiftObj B S hS iΛ toS hk p x₀ hx₀ hx V
      (fromLiftObj B S hS iΛ toS hk p x₀ hx₀ hx V y) rfl = y := by
  rfl

include hx₀ hx in
/-- A morphism of deformations over `k[V]` whose arrow of `𝒞_Λ` is the comparison of the two
presentations has underlying arrow a comparison isomorphism on bases. -/
private theorem deformationMorphism_map (V : FGModuleCat.{u} k)
    (d e : DeformationObject iΛ (p ⋙ Over.post B.inclusion) x₀ hx₀)
    (hd : d.algebra = (artinianSquareZeroExtensionFunctor Λ k).obj V)
    (he : e.algebra = (artinianSquareZeroExtensionFunctor Λ k).obj V)
    (m : DeformationMorphism iΛ (p ⋙ Over.post B.inclusion) x₀ hx₀ d e)
    (hm : m.ringHom = eqToHom (hd.trans he.symm)) :
    p.map m.arrow =
      eqToHom ((deformation_point_site B S hS iΛ toS hk p x₀ hx₀ hx V e he).trans
        (deformation_point_site B S hS iΛ toS hk p x₀ hx₀ hx V d hd).symm) := by
  have hab := m.arrow_base
  rw [hm, specMap_ofHom_eqToHom] at hab
  rw [eqToHom_comp_iff, comp_eqToHom_iff] at hab
  simp only [eqToHom_trans] at hab
  exact hom_eq_eqToHom B S hS _ _ hab


/-- A morphism of lifts over the identity is a comparison isomorphism on bases. -/
private theorem liftMor_map (V : FGModuleCat.{u} k)
    (y y' : liftFiber B S hS toS hk p x₀ hx V) (ψ : y ⟶ y') :
    p.map ψ.1.right =
      eqToHom ((congrArg Under.right y.2).trans (congrArg Under.right y'.2).symm) := by
  have := ψ.2
  have h := IsHomLift.fac' (Under.post p)
    (𝟙 (Under.mk (eqToHom hx ≫
      squareZeroArrow k B S hS toS hk ((fgSiteModule B hk).obj V)))) ψ.1
  have h2 := congrArg Under.Hom.right h
  simp only [Under.eqToHom_right, Category.id_comp, eqToHom_trans] at h2
  exact h2

include hx₀ hx in
/-- A morphism of deformations over the comparison of presentations, read as a morphism of
the corresponding lifts. -/
private def toLiftMor (V : FGModuleCat.{u} k)
    (d e : DeformationObject iΛ (p ⋙ Over.post B.inclusion) x₀ hx₀)
    (hd : d.algebra = (artinianSquareZeroExtensionFunctor Λ k).obj V)
    (he : e.algebra = (artinianSquareZeroExtensionFunctor Λ k).obj V)
    (m : DeformationMorphism iΛ (p ⋙ Over.post B.inclusion) x₀ hx₀ d e)
    (hm : m.ringHom = eqToHom (hd.trans he.symm)) :
    toLiftObj B S hS iΛ toS hk p x₀ hx₀ hx V e he ⟶
      toLiftObj B S hS iΛ toS hk p x₀ hx₀ hx V d hd := by
  refine ⟨Under.homMk m.arrow m.triangle, ?_⟩
  refine IsHomLift.of_fac' (Under.post p) _ _
    (toLiftObj B S hS iΛ toS hk p x₀ hx₀ hx V e he).2
    (toLiftObj B S hS iΛ toS hk p x₀ hx₀ hx V d hd).2 ?_
  apply Under.UnderMorphism.ext
  simp only [Under.eqToHom_right, Category.id_comp, eqToHom_trans]
  exact deformationMorphism_map B S hS iΛ toS hk p x₀ hx₀ hx V d e hd he m hm

include hx₀ hx in
/-- A morphism of lifts, read as a morphism of the corresponding deformations. -/
private def fromLiftMor (V : FGModuleCat.{u} k)
    (y y' : liftFiber B S hS toS hk p x₀ hx V) (ψ : y ⟶ y') :
    DeformationMorphism iΛ (p ⋙ Over.post B.inclusion) x₀ hx₀
      (fromLiftObj B S hS iΛ toS hk p x₀ hx₀ hx V y')
      (fromLiftObj B S hS iΛ toS hk p x₀ hx₀ hx V y) where
  ringHom := 𝟙 _
  arrow := ψ.1.right
  triangle := Under.w ψ.1
  arrow_base := by
    have hψ := liftMor_map B S hS toS hk p x₀ hx V y y' ψ
    simp only [Functor.comp_map, hψ, eqToHom_map, Over.eqToHom_left, eqToHom_trans]
    simp
    rfl

end Lift


section Classes

attribute [local instance] PredeformationConstruction.category

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
  (iΛ : Spec (.of Λ) ⟶ S) (toS : Spec (.of k) ⟶ S) (hk : B.Contains (Spec (.of k)))
  {X : Type v} [Category.{w} X] (p : X ⥤ BigFppfOver B S hS) (hp : p.IsFiberedInGroupoids)
  (x₀ : X)
  (hx₀ : (p ⋙ Over.post B.inclusion).obj x₀ =
    Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
  (hx : p.obj x₀ = algebraOver k B S hS toS hk)

/-- A morphism of the fibre over an object of `𝒞_Λ` has the comparison of presentations as
its arrow of `𝒞_Λ`. -/
private theorem fiberMor_ringHom {A : ArtinianLocalAlgCat.{u, u, u} Λ k}
    (z z' : Functor.Fiber
      (predeformationCategory iΛ (p ⋙ Over.post B.inclusion) x₀ hx₀).projection A)
    (f : z ⟶ z') :
    (f.1 : DeformationMorphism iΛ (p ⋙ Over.post B.inclusion) x₀ hx₀ z.1 z'.1).ringHom =
      eqToHom (z.2.trans z'.2.symm) := by
  have := f.2
  have h := IsHomLift.fac'
    (predeformationCategory iΛ (p ⋙ Over.post B.inclusion) x₀ hx₀).projection (𝟙 A) f.1
  simp only [Category.id_comp, eqToHom_trans] at h
  exact h

include hx₀ hx in
/-- A deformation in the fibre over `k[V]`, read as a lift of the point. -/
@[implicit_reducible]
private def toLiftFib (V : FGModuleCat.{u} k)
    (z : Functor.Fiber (predeformationCategory iΛ (p ⋙ Over.post B.inclusion) x₀ hx₀).projection
      ((artinianSquareZeroExtensionFunctor Λ k).obj V)) :
    liftFiber B S hS toS hk p x₀ hx V :=
  toLiftObj B S hS iΛ toS hk p x₀ hx₀ hx V z.1 z.2

include hx₀ hx in
/-- A lift of the point, read as a deformation in the fibre over `k[V]`. -/
private def fromLiftFib (V : FGModuleCat.{u} k)
    (y : liftFiber B S hS toS hk p x₀ hx V) :
    Functor.Fiber (predeformationCategory iΛ (p ⋙ Over.post B.inclusion) x₀ hx₀).projection
      ((artinianSquareZeroExtensionFunctor Λ k).obj V) :=
  ⟨fromLiftObj B S hS iΛ toS hk p x₀ hx₀ hx V y, rfl⟩

include hx₀ hx hp in
/-- Isomorphic deformations have isomorphic associated lifts. -/
private theorem toLiftFib_isIsomorphic (V : FGModuleCat.{u} k)
    (z z' : Functor.Fiber (predeformationCategory iΛ (p ⋙ Over.post B.inclusion) x₀ hx₀).projection
      ((artinianSquareZeroExtensionFunctor Λ k).obj V))
    (h : IsIsomorphic z z') :
    IsIsomorphic (toLiftFib B S hS iΛ toS hk p x₀ hx₀ hx V z)
      (toLiftFib B S hS iΛ toS hk p x₀ hx₀ hx V z') := by
  obtain ⟨e⟩ := h
  have : IsGroupoid (liftFiber B S hS toS hk p x₀ hx V) :=
    (underPost_isFiberedInGroupoids p hp x₀).fiber_isGroupoid _
  let φ := toLiftMor B S hS iΛ toS hk p x₀ hx₀ hx V z.1 z'.1 z.2 z'.2 e.hom.1
    (fiberMor_ringHom B S hS iΛ p x₀ hx₀ z z' e.hom)
  have : IsIso φ := IsGroupoid.all_isIso φ
  exact ⟨(asIso φ).symm⟩

include hx₀ hx in
/-- The deformation morphism attached to a morphism of lifts lies over the identity. -/
private theorem fromLiftMor_isHomLift (V : FGModuleCat.{u} k)
    {y y' : liftFiber B S hS toS hk p x₀ hx V} (ψ : y ⟶ y') :
    (predeformationCategory iΛ (p ⋙ Over.post B.inclusion) x₀ hx₀).projection.IsHomLift
      (𝟙 ((artinianSquareZeroExtensionFunctor Λ k).obj V))
      (fromLiftMor B S hS iΛ toS hk p x₀ hx₀ hx V y y' ψ :
        (fromLiftFib B S hS iΛ toS hk p x₀ hx₀ hx V y').1 ⟶
          (fromLiftFib B S hS iΛ toS hk p x₀ hx₀ hx V y).1) := by
  refine IsHomLift.of_fac' _ _ _ rfl rfl ?_
  simp only [eqToHom_refl, Category.comp_id]
  rfl

include hx₀ hx in
/-- A morphism of lifts, read as a morphism of the fibre of deformations. -/
private def fromLiftFibMor (V : FGModuleCat.{u} k)
    {y y' : liftFiber B S hS toS hk p x₀ hx V} (ψ : y ⟶ y') :
    fromLiftFib B S hS iΛ toS hk p x₀ hx₀ hx V y' ⟶
      fromLiftFib B S hS iΛ toS hk p x₀ hx₀ hx V y :=
  ⟨fromLiftMor B S hS iΛ toS hk p x₀ hx₀ hx V y y' ψ,
    fromLiftMor_isHomLift B S hS iΛ toS hk p x₀ hx₀ hx V ψ⟩

include hx₀ hx in
/-- Isomorphic lifts give isomorphic deformations. -/
private theorem fromLiftFib_isIsomorphic (V : FGModuleCat.{u} k)
    (y y' : liftFiber B S hS toS hk p x₀ hx V) (h : IsIsomorphic y y') :
    IsIsomorphic (fromLiftFib B S hS iΛ toS hk p x₀ hx₀ hx V y)
      (fromLiftFib B S hS iΛ toS hk p x₀ hx₀ hx V y') := by
  obtain ⟨e⟩ := h
  refine ⟨⟨fromLiftFibMor B S hS iΛ toS hk p x₀ hx₀ hx V e.inv,
    fromLiftFibMor B S hS iΛ toS hk p x₀ hx₀ hx V e.hom, ?_, ?_⟩⟩
  · apply Subtype.ext
    refine DeformationMorphism.ext_of_components iΛ (p ⋙ Over.post B.inclusion) x₀ hx₀
      (by rfl) ?_
    show (e.hom.1).right ≫ (e.inv.1).right = 𝟙 _
    exact congrArg (fun t : y ⟶ y => (t.1).right) e.hom_inv_id
  · apply Subtype.ext
    refine DeformationMorphism.ext_of_components iΛ (p ⋙ Over.post B.inclusion) x₀ hx₀
      (by rfl) ?_
    show (e.inv.1).right ≫ (e.hom.1).right = 𝟙 _
    exact congrArg (fun t : y' ⟶ y' => (t.1).right) e.inv_hom_id

include hx₀ hx in
/-- The classes of deformations over `k[V]` are the classes of lifts of the point along the
square-zero immersion. -/
private def liftClassEquiv (V : FGModuleCat.{u} k) :
    Quotient (isIsomorphicSetoid (Functor.Fiber
      (predeformationCategory iΛ (p ⋙ Over.post B.inclusion) x₀ hx₀).projection
        ((artinianSquareZeroExtensionFunctor Λ k).obj V))) ≃
      squareZeroLiftClasses k B S hS toS hk p x₀ hx ((fgSiteModule B hk).obj V) where
  toFun := Quotient.map (toLiftFib B S hS iΛ toS hk p x₀ hx₀ hx V)
    (toLiftFib_isIsomorphic B S hS iΛ toS hk p hp x₀ hx₀ hx V)
  invFun := Quotient.map (fromLiftFib B S hS iΛ toS hk p x₀ hx₀ hx V)
    (fromLiftFib_isIsomorphic B S hS iΛ toS hk p x₀ hx₀ hx V)
  left_inv q := by
    induction q using Quotient.ind with
    | _ z =>
      exact congrArg (Quotient.mk _)
        (Subtype.ext (fromLiftObj_toLiftObj B S hS iΛ toS hk p x₀ hx₀ hx V z.1 z.2))
  right_inv q := by
    induction q using Quotient.ind with
    | _ y =>
      exact congrArg (Quotient.mk _)
        (toLiftObj_fromLiftObj B S hS iΛ toS hk p x₀ hx₀ hx V y)

include hx₀ hx in
/-- The arrow realizing a lift over `k[W]` as the pullback of a lift over `k[V]` lies over
the induced arrow of `𝒞_Λ`. -/
private theorem liftTransition_arrow_base {V W : FGModuleCat.{u} k} (f : V ⟶ W)
    (a' : liftFiber B S hS toS hk p x₀ hx V) (b' : liftFiber B S hS toS hk p x₀ hx W)
    (φ : b'.1.right ⟶ a'.1.right)
    [p.IsHomLift (squareZeroOverMap k B S hS toS ((fgSiteModule B hk).map f)) φ] :
    eqToHom (congrArg Over.left (lift_base B S hS iΛ toS hk p x₀ hx₀ hx W b')).symm ≫
      ((p ⋙ Over.post B.inclusion).map φ).left ≫
        eqToHom (congrArg Over.left
          (lift_base B S hS iΛ toS hk p x₀ hx₀ hx V a')) =
      Spec.map (CommRingCat.ofHom
        ((artinianSquareZeroExtensionFunctor Λ k).map f).hom.toRingHom) := by
  have h := IsHomLift.fac' p
    (squareZeroOverMap k B S hS toS ((fgSiteModule B hk).map f)) φ
  rw [Functor.comp_map, h]
  simp only [Functor.map_comp, Over.comp_left, Over.eqToHom_left, eqToHom_map,
    Category.assoc, eqToHom_trans]
  rw [← Category.assoc, eqToHom_trans]
  exact (Category.id_comp _).trans (Category.comp_id _)

include hx₀ hx in
/-- The comparison of classes is natural: a deformation class is carried to the class of any
pullback of the corresponding lift. -/
private theorem classOf_map_eq
    (hcof : IsCofiberedInGroupoids (BasedCategory.ofFunctor
      (predeformationCategory iΛ (p ⋙ Over.post B.inclusion) x₀ hx₀).projection).p)
    {V W : FGModuleCat.{u} k} (f : V ⟶ W)
    (z : Functor.Fiber
      (predeformationCategory iΛ (p ⋙ Over.post B.inclusion) x₀ hx₀).projection
        ((artinianSquareZeroExtensionFunctor Λ k).obj V))
    (y' : liftFiber B S hS toS hk p x₀ hx W)
    (hpb : IsPullbackOfSquareZeroLift k B S hS toS hk p x₀ hx
      ((fgSiteModule B hk).map f)
      (Quotient.mk _ (toLiftFib B S hS iΛ toS hk p x₀ hx₀ hx V z))
      (Quotient.mk _ y')) :
    (isomorphismClasses (BasedCategory.ofFunctor
          (predeformationCategory iΛ (p ⋙ Over.post B.inclusion) x₀ hx₀).projection)
        hcof).map ((artinianSquareZeroExtensionFunctor Λ k).map f)
        (classOf _ hcof z) =
      classOf _ hcof (fromLiftFib B S hS iΛ toS hk p x₀ hx₀ hx W y') := by
  obtain ⟨a', b'', ha', hb'', φ, hφ, htri⟩ := hpb
  have : p.IsHomLift (squareZeroOverMap k B S hS toS ((fgSiteModule B hk).map f)) φ :=
    hφ.toIsHomLift
  let m : DeformationMorphism iΛ (p ⋙ Over.post B.inclusion) x₀ hx₀
      (fromLiftObj B S hS iΛ toS hk p x₀ hx₀ hx V a')
      (fromLiftObj B S hS iΛ toS hk p x₀ hx₀ hx W b'') :=
    { ringHom := (artinianSquareZeroExtensionFunctor Λ k).map f
      arrow := φ
      triangle := htri
      arrow_base := liftTransition_arrow_base B S hS iΛ toS hk p x₀ hx₀ hx f a' b'' φ }
  have hml0 : (predeformationCategory iΛ (p ⋙ Over.post B.inclusion)
      x₀ hx₀).projection.IsHomLift ((artinianSquareZeroExtensionFunctor Λ k).map f)
      (m : (fromLiftFib B S hS iΛ toS hk p x₀ hx₀ hx V a').1 ⟶
        (fromLiftFib B S hS iΛ toS hk p x₀ hx₀ hx W b'').1) :=
    IsHomLift.of_fac' _ _ _ rfl rfl
      (by simp only [eqToHom_refl, Category.id_comp, Category.comp_id]; rfl)
  have hml : (BasedCategory.ofFunctor
      (predeformationCategory iΛ (p ⋙ Over.post B.inclusion) x₀ hx₀).projection).p.IsHomLift
      ((artinianSquareZeroExtensionFunctor Λ k).map f)
      (m : (fromLiftFib B S hS iΛ toS hk p x₀ hx₀ hx V a').1 ⟶
        (fromLiftFib B S hS iΛ toS hk p x₀ hx₀ hx W b'').1) := hml0
  have hzz : fromLiftFib B S hS iΛ toS hk p x₀ hx₀ hx V
      (toLiftFib B S hS iΛ toS hk p x₀ hx₀ hx V z) = z :=
    Subtype.ext (fromLiftObj_toLiftObj B S hS iΛ toS hk p x₀ hx₀ hx V z.1 z.2)
  have hz : classOf _ hcof z =
      classOf _ hcof (fromLiftFib B S hS iΛ toS hk p x₀ hx₀ hx V a') := by
    refine (classOf_eq_of_isIsomorphic _ hcof _ _ ?_).symm
    rw [← hzz]
    exact fromLiftFib_isIsomorphic B S hS iΛ toS hk p x₀ hx₀ hx V a'
      (toLiftFib B S hS iΛ toS hk p x₀ hx₀ hx V z) (Quotient.exact ha')
  have hy : classOf _ hcof (fromLiftFib B S hS iΛ toS hk p x₀ hx₀ hx W b'') =
      classOf _ hcof (fromLiftFib B S hS iΛ toS hk p x₀ hx₀ hx W y') :=
    classOf_eq_of_isIsomorphic _ hcof _ _
      (fromLiftFib_isIsomorphic B S hS iΛ toS hk p x₀ hx₀ hx W b'' y' (Quotient.exact hb''))
  rw [hz, ← hy]
  exact @map_classOf _ _ _ hcof _ _ _ _ _ m hml


include hx₀ hx hp in
/-- **Deformation classes over `k[V]` are lift classes, naturally in `V`**, the class of a
deformation going to the class of its arrow, and a map `V ⟶ W` carrying a deformation class to
every pullback of its lift class. -/
public theorem exists_deformationClassEquiv_squareZeroLiftClasses
    (hcof : IsCofiberedInGroupoids (BasedCategory.ofFunctor
      (predeformationCategory iΛ (p ⋙ Over.post B.inclusion) x₀ hx₀).projection).p) :
    ∃ c : ∀ V : FGModuleCat.{u} k,
        (isomorphismClasses (BasedCategory.ofFunctor
          (predeformationCategory iΛ (p ⋙ Over.post B.inclusion) x₀ hx₀).projection) hcof).obj
            ((artinianSquareZeroExtensionFunctor Λ k).obj V) ≃
          squareZeroLiftClasses k B S hS toS hk p x₀ hx ((fgSiteModule B hk).obj V),
      (∀ (V : FGModuleCat.{u} k) (z : Functor.Fiber
          (predeformationCategory iΛ (p ⋙ Over.post B.inclusion) x₀ hx₀).projection
            ((artinianSquareZeroExtensionFunctor Λ k).obj V)),
        ∃ y : (Under.post p).Fiber (Under.mk (eqToHom hx ≫
            squareZeroArrow k B S hS toS hk ((fgSiteModule B hk).obj V))),
          c V (classOf _ hcof z) = Quotient.mk _ y ∧
            ∃ (η : y.1.right ≅ ((predeformationCategory iΛ (p ⋙ Over.post B.inclusion)
                x₀ hx₀).objects z.1).point)
              (hbase : p.obj y.1.right = p.obj ((predeformationCategory iΛ
                (p ⋙ Over.post B.inclusion) x₀ hx₀).objects z.1).point),
              p.map η.hom = eqToHom hbase ∧ y.1.hom ≫ η.hom =
                ((predeformationCategory iΛ (p ⋙ Over.post B.inclusion) x₀ hx₀).objects
                  z.1).arrow) ∧
      ∀ {V W : FGModuleCat.{u} k} (f : V ⟶ W) t b,
        IsPullbackOfSquareZeroLift k B S hS toS hk p x₀ hx ((fgSiteModule B hk).map f)
          (c V t) b →
        c W ((isomorphismClasses _ hcof).map ((artinianSquareZeroExtensionFunctor Λ k).map f) t) =
          b := by
  let c : ∀ V : FGModuleCat.{u} k, _ := fun V => (Equiv.cast (isomorphismClasses_obj _ hcof
    _)).trans (liftClassEquiv B S hS iΛ toS hk p hp x₀ hx₀ hx V)
  have hc : ∀ V z, c V (classOf _ hcof z) =
      Quotient.mk _ (toLiftFib B S hS iΛ toS hk p x₀ hx₀ hx V z) := fun V z =>
    congrArg (liftClassEquiv B S hS iΛ toS hk p hp x₀ hx₀ hx V) (classOf_eq _ hcof z)
  refine ⟨c, fun V z => ⟨_, hc V z, Iso.refl _, rfl, p.map_id _, Category.comp_id _⟩, ?_⟩
  intro V W f t b hpb
  obtain ⟨z, rfl⟩ := classOf_surjective _ hcof _ t
  induction b using Quotient.ind with
  | _ y' =>
    rw [hc V z] at hpb
    rw [classOf_map_eq B S hS iΛ toS hk p x₀ hx₀ hx hcof f z y' hpb, hc W]
    exact congrArg (Quotient.mk _) (toLiftObj_fromLiftObj B S hS iΛ toS hk p x₀ hx₀ hx W y')

end Classes


section LinearComparison

universe uu uu₁

/-- On types, the comparison isomorphism of an equality acts by transport. -/
private theorem types_eqToHom_apply {Xt Yt : Type uu₁} (h : Xt = Yt) (t : Xt) :
    ConcreteCategory.hom (eqToHom h : Xt ⟶ Yt) t = cast h t := by
  subst h; rfl

/-- Transport along an equality of types and back is the identity. -/
private theorem cast_cast_self {α β : Type uu₁} (h : α = β) (h' : β = α) (s : α) :
    cast h' (cast h s) = s := by
  subst h; rfl

/-- Two linear lifts of naturally isomorphic set-valued functors on finite-dimensional
vector spaces take linearly isomorphic values, and the isomorphism is the given one. -/
private theorem exists_linearEquiv_of_natIso {R : Type uu} [CommRing R]
    (F G : FGModuleCat.{uu} R ⥤ Type uu₁)
    [Limits.PreservesFiniteProducts F] [Unique (F.obj (FGModuleCat.of R PUnit.{uu + 1}))]
    [Limits.PreservesFiniteProducts G] [Unique (G.obj (FGModuleCat.of R PUnit.{uu + 1}))]
    (A : Deformation.LinearFunctorLift R F) (A' : Deformation.LinearFunctorLift R G)
    (α : F ≅ G) (V : FGModuleCat.{uu} R) :
    ∃ e : (A.functor.obj V : Type uu₁) ≃ₗ[R] (A'.functor.obj V : Type uu₁),
      ∀ t : F.obj V, e (cast (congrArg (fun H : FGModuleCat.{uu} R ⥤ Type uu₁ => H.obj V)
          A.forget_comp).symm t) =
        cast (congrArg (fun H : FGModuleCat.{uu} R ⥤ Type uu₁ => H.obj V)
          A'.forget_comp).symm (α.hom.app V t) := by
  obtain ⟨huF⟩ := Deformation.fgModuleCat_linearFunctorLift_unique R F
  obtain ⟨huG⟩ := Deformation.fgModuleCat_linearFunctorLift_unique R G
  obtain rfl : Deformation.fgModuleCatLinearFunctorLift R F = A := Subsingleton.elim _ _
  obtain rfl : Deformation.fgModuleCatLinearFunctorLift R G = A' := Subsingleton.elim _ _
  obtain ⟨τ, hτ, -⟩ := Deformation.fgModuleCat_linearFunctorLift_natTrans R F G α.hom
  have hiso : IsIso (Functor.whiskerRight τ (forget (ModuleCat.{uu₁} R))) := by
    rw [hτ]; infer_instance
  have happ : IsIso ((Functor.whiskerRight τ (forget (ModuleCat.{uu₁} R))).app V) :=
    inferInstance
  have hbij : Function.Bijective (τ.app V).hom :=
    (isIso_iff_bijective _).1 happ
  refine ⟨LinearEquiv.ofBijective (τ.app V).hom hbij, ?_⟩
  have key : ∀ t, (LinearEquiv.ofBijective (τ.app V).hom hbij) t =
      cast (congrArg (fun H : FGModuleCat.{uu} R ⥤ Type uu₁ => H.obj V)
          (Deformation.fgModuleCatLinearFunctorLift R G).forget_comp).symm
        (α.hom.app V (cast (congrArg (fun H : FGModuleCat.{uu} R ⥤ Type uu₁ => H.obj V)
          (Deformation.fgModuleCatLinearFunctorLift R F).forget_comp) t)) := by
    intro t
    have hc : (Functor.whiskerRight τ (forget (ModuleCat.{uu₁} R))).app V t =
      (eqToHom (Deformation.fgModuleCatLinearFunctorLift R F).forget_comp ≫ α.hom ≫
        eqToHom (Deformation.fgModuleCatLinearFunctorLift R G).forget_comp.symm).app V t := by
      rw [hτ]
    simpa [eqToHom_app, Functor.whiskerRight_app, types_eqToHom_apply] using hc
  intro t
  rw [key, cast_cast_self]

end LinearComparison

section Comparison

attribute [local instance] PredeformationConstruction.category

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
  (iΛ : Spec (.of Λ) ⟶ S) (toS : Spec (.of k) ⟶ S) (hk : B.Contains (Spec (.of k)))
  {X : Type v} [Category.{w} X] (p : X ⥤ BigFppfOver B S hS) (hp : p.IsFiberedInGroupoids)
  (hRS : SatisfiesRSStar B S hS p hp) (x₀ : X)
  (hx₀ : (p ⋙ Over.post B.inclusion).obj x₀ =
    Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
  (hx : p.obj x₀ = algebraOver k B S hS toS hk)
  (hcof : IsCofiberedInGroupoids (BasedCategory.ofFunctor
    (predeformationCategory iΛ (p ⋙ Over.post B.inclusion) x₀ hx₀).projection).p)

/-- Deformation classes over the trivial square-zero extensions, as a functor of the
vector space. -/
private abbrev deformationClassFunctor : FGModuleCat.{u} k ⥤ Type (max (u + 1) v w) :=
  artinianSquareZeroExtensionFunctor Λ k ⋙
    isomorphismClasses (BasedCategory.ofFunctor
      (predeformationCategory iΛ (p ⋙ Over.post B.inclusion) x₀ hx₀).projection) hcof

/-- The tangent functor restricted to the finite-dimensional vector spaces. -/
private abbrev tangentLinearFunctor :
    FGModuleCat.{u} k ⥤ ModuleCat.{max (u + 1) v w} k :=
  fgSiteModule B hk ⋙ (tangentFunctor k B S hS toS hk p x₀ hx hp hRS).functor

/-- The set-valued functor underlying the tangent functor, restricted to the
finite-dimensional vector spaces. -/
private abbrev tangentSetFunctor : FGModuleCat.{u} k ⥤ Type (max (u + 1) v w) :=
  tangentLinearFunctor B S hS toS hk p hp hRS x₀ hx ⋙
    forget (ModuleCat.{max (u + 1) v w} k)

/-- The comparison of deformation classes with lift classes at a fixed vector space. -/
private def classCompare (V : FGModuleCat.{u} k) :
    (deformationClassFunctor B S hS iΛ p x₀ hx₀ hcof).obj V ≃
      (tangentSetFunctor B S hS toS hk p hp hRS x₀ hx).obj V :=
  (Equiv.cast (isomorphismClasses_obj _ hcof
      ((artinianSquareZeroExtensionFunctor Λ k).obj V))).trans
    ((liftClassEquiv B S hS iΛ toS hk p hp x₀ hx₀ hx V).trans
      ((tangentFunctor k B S hS toS hk p x₀ hx hp hRS).liftEquiv
        ((fgSiteModule B hk).obj V)).symm)

/-- The comparison carries the class of a deformation to the class of the corresponding
lift. -/
private theorem classCompare_classOf (V : FGModuleCat.{u} k)
    (z : Functor.Fiber
      (predeformationCategory iΛ (p ⋙ Over.post B.inclusion) x₀ hx₀).projection
        ((artinianSquareZeroExtensionFunctor Λ k).obj V)) :
    (tangentFunctor k B S hS toS hk p x₀ hx hp hRS).liftEquiv ((fgSiteModule B hk).obj V)
        (classCompare B S hS iΛ toS hk p hp hRS x₀ hx₀ hx hcof V (classOf _ hcof z)) =
      Quotient.mk _ (toLiftFib B S hS iΛ toS hk p x₀ hx₀ hx V z) := by
  show (tangentFunctor k B S hS toS hk p x₀ hx hp hRS).liftEquiv _
      (((tangentFunctor k B S hS toS hk p x₀ hx hp hRS).liftEquiv _).symm
        (liftClassEquiv B S hS iΛ toS hk p hp x₀ hx₀ hx V
          (cast (isomorphismClasses_obj _ hcof _) (classOf _ hcof z)))) = _
  rw [Equiv.apply_symm_apply, classOf_eq]
  rfl

/-- The comparison of deformation classes with lift classes is natural. -/
private theorem classCompare_naturality {V W : FGModuleCat.{u} k} (f : V ⟶ W)
    (t : (deformationClassFunctor B S hS iΛ p x₀ hx₀ hcof).obj V) :
    classCompare B S hS iΛ toS hk p hp hRS x₀ hx₀ hx hcof W
        ((isomorphismClasses _ hcof).map
          ((artinianSquareZeroExtensionFunctor Λ k).map f) t) =
      (tangentFunctor k B S hS toS hk p x₀ hx hp hRS).functor.map
        ((fgSiteModule B hk).map f)
        (classCompare B S hS iΛ toS hk p hp hRS x₀ hx₀ hx hcof V t) := by
  obtain ⟨z, rfl⟩ := classOf_surjective _ hcof _ t
  have hnat := (tangentFunctor k B S hS toS hk p x₀ hx hp hRS).liftEquiv_natural
    ((fgSiteModule B hk).map f)
    (classCompare B S hS iΛ toS hk p hp hRS x₀ hx₀ hx hcof V (classOf _ hcof z))
  rw [classCompare_classOf B S hS iΛ toS hk p hp hRS x₀ hx₀ hx hcof V z] at hnat
  obtain ⟨y', hy'⟩ := Quotient.exists_rep
    ((tangentFunctor k B S hS toS hk p x₀ hx hp hRS).liftEquiv
      ((fgSiteModule B hk).obj W)
      ((tangentFunctor k B S hS toS hk p x₀ hx hp hRS).functor.map
        ((fgSiteModule B hk).map f)
        (classCompare B S hS iΛ toS hk p hp hRS x₀ hx₀ hx hcof V (classOf _ hcof z))))
  rw [← hy'] at hnat
  have hmap := classOf_map_eq B S hS iΛ toS hk p x₀ hx₀ hx hcof f z y' hnat
  apply ((tangentFunctor k B S hS toS hk p x₀ hx hp hRS).liftEquiv
    ((fgSiteModule B hk).obj W)).injective
  rw [hmap, classCompare_classOf B S hS iΛ toS hk p hp hRS x₀ hx₀ hx hcof W, ← hy']
  exact congrArg (Quotient.mk _)
    (toLiftObj_fromLiftObj B S hS iΛ toS hk p x₀ hx₀ hx W y')

/-- The natural identification of deformation classes with lift classes. -/
private def classCompareIso :
    deformationClassFunctor B S hS iΛ p x₀ hx₀ hcof ≅
      tangentSetFunctor B S hS toS hk p hp hRS x₀ hx :=
  NatIso.ofComponents
    (fun V => Equiv.toIso (classCompare B S hS iΛ toS hk p hp hRS x₀ hx₀ hx hcof V))
    (fun {V W} f => by
      ext t
      exact classCompare_naturality B S hS iΛ toS hk p hp hRS x₀ hx₀ hx hcof f t)

/-- The tangent functor is additive on finite-dimensional vector spaces. -/
private instance tangentLinearFunctor_additive :
    (tangentLinearFunctor B S hS toS hk p hp hRS x₀ hx).Additive :=
  inferInstance

/-- The tangent functor is `k`-linear on finite-dimensional vector spaces. -/
private instance tangentLinearFunctor_linear :
    (tangentLinearFunctor B S hS toS hk p hp hRS x₀ hx).Linear k :=
  inferInstance

/-- The underlying set-valued tangent functor preserves finite products. -/
private instance tangentSetFunctor_preservesFiniteProducts :
    Limits.PreservesFiniteProducts (tangentSetFunctor B S hS toS hk p hp hRS x₀ hx) :=
  inferInstance

include hRS hx₀ in
/-- The tangent space of the deformation category is linearly identified with the value of
the tangent functor at the rank-one vector space, compatibly with the comparison of
classes. -/
private theorem exists_tangentLinearEquiv
    (hpre : IsPredeformationCategory (BasedCategory.ofFunctor
      (predeformationCategory iΛ (p ⋙ Over.post B.inclusion) x₀ hx₀).projection).p)
    (hS2 : SchlessingerConditionS2 (CategoryOfElements.π
      (isomorphismClasses (BasedCategory.ofFunctor
        (predeformationCategory iΛ (p ⋙ Over.post B.inclusion) x₀ hx₀).projection) hcof)))
    [Fact (IsPredeformationCategory (BasedCategory.ofFunctor
      (predeformationCategory iΛ (p ⋙ Over.post B.inclusion) x₀ hx₀).projection).p)]
    [Fact (SchlessingerConditionS2 (CategoryOfElements.π
      (isomorphismClasses (BasedCategory.ofFunctor
        (predeformationCategory iΛ (p ⋙ Over.post B.inclusion) x₀ hx₀).projection) hcof)))] :
    ∃ e : artinianTangentSpace Λ k (isomorphismClasses (BasedCategory.ofFunctor
        (predeformationCategory iΛ (p ⋙ Over.post B.inclusion) x₀ hx₀).projection) hcof) ≃ₗ[k]
        (tangentLinearFunctor B S hS toS hk p hp hRS x₀ hx).obj (FGModuleCat.of k k),
      ∀ t, e t = classCompare B S hS iΛ toS hk p hp hRS x₀ hx₀ hx hcof
        (FGModuleCat.of k k) t := by
  have hcond := associatedSquareZeroFunctor_conditions (BasedCategory.ofFunctor
    (predeformationCategory iΛ (p ⋙ Over.post B.inclusion) x₀ hx₀).projection) hpre hS2
  have hUL : Unique ((deformationClassFunctor B S hS iΛ p x₀ hx₀ hcof).obj
      (FGModuleCat.of k PUnit.{u + 1})) :=
    @Unique.mk' _ ⟨hcond.1.some⟩ hcond.2.1
  have hUR : Unique ((tangentSetFunctor B S hS toS hk p hp hRS x₀ hx).obj
      (FGModuleCat.of k PUnit.{u + 1})) :=
    (classCompare B S hS iΛ toS hk p hp hRS x₀ hx₀ hx hcof
      (FGModuleCat.of k PUnit.{u + 1})).symm.unique
  have : Limits.PreservesFiniteProducts
      (deformationClassFunctor B S hS iΛ p x₀ hx₀ hcof) :=
    ⟨fun _ => Limits.preservesLimitsOfShape_of_natIso
      (classCompareIso B S hS iΛ toS hk p hp hRS x₀ hx₀ hx hcof).symm⟩
  obtain ⟨e, he⟩ := exists_linearEquiv_of_natIso
    (deformationClassFunctor B S hS iΛ p x₀ hx₀ hcof)
    (tangentSetFunctor B S hS toS hk p hp hRS x₀ hx)
    (associatedTangentSpaceModuleStructureUnlifted _ hpre hS2)
    ⟨tangentLinearFunctor B S hS toS hk p hp hRS x₀ hx, rfl⟩
    (classCompareIso B S hS iΛ toS hk p hp hRS x₀ hx₀ hx hcof)
    (FGModuleCat.of k k)
  refine ⟨(eqRecModuleDataLinearEquiv
    (associatedTangentSpaceModuleStructure_carrierUnlifted _ hpre hS2)
    ⟨_, _⟩).symm.trans e, fun t => ?_⟩
  exact he t

end Comparison

section Statement

attribute [local instance] PredeformationConstruction.category

/-- **Stacks Project, Tag 0D18, tangent spaces.** For a category fibred in groupoids over the
big fppf site of a locally Noetherian scheme satisfying (RS*), the tangent space of the
deformation category of a finite-type field-valued point is the value of the tangent functor
of Tag 07Y9 at the rank-one vector space. Both sides carry the unique linear structure
compatible with finite products (Tag 06I6), and the identification carries the class of a
deformation to the class of the corresponding lift. -/
@[stacks 0D18 "tangent spaces"]
public theorem tangentSpace_deformationCategory_linearEquiv
    (B : BigFppfSite.{u}) (S : Scheme.{u}) [IsLocallyNoetherian S] (hS : B.Contains S)
    {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
    (iΛ : Spec (.of Λ) ⟶ S) (toS : Spec (.of k) ⟶ S)
    (hk : B.Contains (Spec (.of k)))
    (hfin : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
    (hqc : QuasiCompact (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
    {X : Type v} [Category.{w} X] (p : X ⥤ BigFppfOver B S hS)
    (hp : p.IsFiberedInGroupoids) (hRS : SatisfiesRSStar B S hS p hp) (x₀ : X)
    (hx₀ : (p ⋙ Over.post B.inclusion).obj x₀ =
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
    (hx : p.obj x₀ = algebraOver k B S hS toS hk) :
    let D := predeformationCategory iΛ (p ⋙ Over.post B.inclusion) x₀ hx₀
    let 𝓕 := BasedCategory.ofFunctor D.projection
    let hD : Deformation.IsDeformationCategory D.projection :=
      isDeformationCategory_predeformationCategory_of_satisfiesRSStar B S hS p hp hRS iΛ x₀
        hx₀ hfin hqc
    letI : Fact (IsPredeformationCategory 𝓕.p) := ⟨hD.predeformation⟩
    letI : Fact (SchlessingerConditionS2 (CategoryOfElements.π
      (isomorphismClasses 𝓕 hD.predeformation.cofibered))) :=
      ⟨schlessingerConditionS2_isomorphismClasses_of_isDeformationCategory 𝓕 hD⟩
    let M : SiteModule k B := (fgSiteModule B hk).obj (FGModuleCat.of k k)
    let L := tangentFunctor k B S hS toS hk p x₀ hx hp hRS
    ∃ e : artinianTangentSpace Λ k (isomorphismClasses 𝓕 hD.predeformation.cofibered) ≃ₗ[k]
        L.functor.obj M,
      ∀ z : D.projection.Fiber ((artinianSquareZeroExtensionFunctor Λ k).obj
          (FGModuleCat.of k k)),
        ∃ y : (Under.post p).Fiber
            (Under.mk (eqToHom hx ≫ squareZeroArrow k B S hS toS hk M)),
          L.liftEquiv M (e (classOf 𝓕 hD.predeformation.cofibered z)) = Quotient.mk _ y ∧
            ∃ (η : y.1.right ≅ (D.objects z.1).point)
              (hbase : p.obj y.1.right = p.obj (D.objects z.1).point),
              p.map η.hom = eqToHom hbase ∧
                y.1.hom ≫ η.hom = (D.objects z.1).arrow := by
  intro D 𝓕 hD M L
  let : Fact (IsPredeformationCategory 𝓕.p) := ⟨hD.predeformation⟩
  let : Fact (SchlessingerConditionS2 (CategoryOfElements.π
    (isomorphismClasses 𝓕 hD.predeformation.cofibered))) :=
    ⟨schlessingerConditionS2_isomorphismClasses_of_isDeformationCategory 𝓕 hD⟩
  obtain ⟨e, he⟩ := exists_tangentLinearEquiv B S hS iΛ toS hk p hp hRS x₀ hx₀ hx
    hD.predeformation.cofibered hD.predeformation
    (schlessingerConditionS2_isomorphismClasses_of_isDeformationCategory 𝓕 hD)
  refine ⟨e, fun z => ⟨toLiftFib B S hS iΛ toS hk p x₀ hx₀ hx (FGModuleCat.of k k) z, ?_,
    Iso.refl _, rfl, p.map_id _, Category.comp_id _⟩⟩
  refine (congrArg (fun t => L.liftEquiv M t)
    (he (classOf 𝓕 hD.predeformation.cofibered z))).trans ?_
  exact classCompare_classOf B S hS iΛ toS hk p hp hRS x₀ hx₀ hx
    hD.predeformation.cofibered (FGModuleCat.of k k) z

end Statement


section CanonicalDualNumbers

variable (Λ k : Type u) [CommRing Λ] [Field k] [Algebra Λ k]

/-- The trivial square-zero extension of `k` by the zero vector space: the residue field,
read as an object of `𝒞_Λ` in the image of the square-zero extension functor. -/
private abbrev dualPointObj : ArtinianLocalAlgCat.{u, u, u} Λ k :=
  (artinianSquareZeroExtensionFunctor Λ k).obj (FGModuleCat.of k PUnit.{u + 1})

/-- The dual numbers over `k`, as the trivial square-zero extension by the rank-one vector
space. -/
@[ega "0 22.1.3" "partial", ega "0 22.1.3.2" "partial"]
private abbrev dualNumbersObj : ArtinianLocalAlgCat.{u, u, u} Λ k :=
  (artinianSquareZeroExtensionFunctor Λ k).obj (FGModuleCat.of k k)

/-- The square-zero extension functor acts on a morphism by the induced map of trivial
square-zero extensions. -/
private theorem artinianSquareZeroExtensionFunctor_map_hom_apply {V W : FGModuleCat.{u} k}
    (f : V ⟶ W) (a : ((artinianSquareZeroExtensionFunctor Λ k).obj V : Type u)) :
    ((artinianSquareZeroExtensionFunctor Λ k).map f).hom a =
      TrivSqZeroExt.map (ModuleCat.Hom.hom f.hom) a := rfl

/-- The canonical inclusion of the residue field into the dual numbers, as the square-zero
extension of the inclusion of the zero module. -/
private def dualInclusion : dualPointObj Λ k ⟶ dualNumbersObj Λ k :=
  (artinianSquareZeroExtensionFunctor Λ k).map 0

/-- The canonical projection of the dual numbers onto the residue field. -/
private def dualProjection : dualNumbersObj Λ k ⟶ dualPointObj Λ k :=
  (artinianSquareZeroExtensionFunctor Λ k).map 0

/-- The canonical inclusion followed by the canonical projection is the identity. -/
private theorem dualInclusion_comp_dualProjection :
    dualInclusion Λ k ≫ dualProjection Λ k = 𝟙 (dualPointObj Λ k) := by
  have h0 : (0 : FGModuleCat.of k PUnit.{u + 1} ⟶ FGModuleCat.of k k) ≫ 0 =
      𝟙 (FGModuleCat.of k PUnit.{u + 1}) :=
    FGModuleCat.hom_ext (LinearMap.ext fun _ => Subsingleton.elim (α := PUnit.{u + 1}) _ _)
  show (artinianSquareZeroExtensionFunctor Λ k).map 0 ≫
    (artinianSquareZeroExtensionFunctor Λ k).map 0 = _
  rw [← CategoryTheory.Functor.map_comp, h0, CategoryTheory.Functor.map_id]

/-- The residue map of the square-zero extension by the zero module is bijective. -/
private theorem bijective_residueMap_dualPointObj :
    Function.Bijective (residueMap (dualPointObj Λ k)) := by
  constructor
  · intro a b hab
    refine TrivSqZeroExt.ext hab ?_
    exact Subsingleton.elim (α := PUnit.{u + 1}) _ _
  · intro a
    exact ⟨((a, 0) : TrivSqZeroExt k PUnit.{u + 1}), rfl⟩

end CanonicalDualNumbers


section InfinitesimalComparison

attribute [local instance] PredeformationConstruction.category

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
  (iΛ : Spec (.of Λ) ⟶ S) (toS : Spec (.of k) ⟶ S) (hk : B.Contains (Spec (.of k)))
  {X : Type v} [Category.{w} X] (p : X ⥤ BigFppfOver B S hS) (hp : p.IsFiberedInGroupoids)
  (x₀ : X)
  (hx₀ : (p ⋙ Over.post B.inclusion).obj x₀ =
    Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
  (hx : p.obj x₀ = algebraOver k B S hS toS hk)

/-- The trivial deformation of the point over the trivial square-zero extension by a
finite-dimensional vector space, read as a lift along the square-zero immersion. -/
private abbrev trivialLift (V : FGModuleCat.{u} k) : liftFiber B S hS toS hk p x₀ hx V :=
  trivialDeformation k B S hS toS hk p x₀ hx hp ((fgSiteModule B hk).obj V)

/-- The canonical arrow of trivial deformations attached to a map of vector spaces. -/
private def trivialTransition {V W : FGModuleCat.{u} k} (f : V ⟶ W) :
    (trivialLift B S hS toS hk p hp x₀ hx W).1 ⟶
      (trivialLift B S hS toS hk p hp x₀ hx V).1 :=
  letI : (Under.post p : Under x₀ ⥤ Under (p.obj x₀)).IsFibered := underPost_isFibered p hp x₀
  Functor.pullbackFiberMap (Under.post p) (liftId k B S hS toS hk p x₀ hx)
    (liftBaseOverMap k B S hS toS hk p x₀ hx ((fgSiteModule B hk).map f))

/-- An arrow of lifts lying over an arrow of thickenings lies, on underlying objects, over
the corresponding arrow of the site. -/
private theorem isHomLift_right_of_underPost {U V : Under (p.obj x₀)} {a b : Under x₀}
    (φ : a ⟶ b) (β : U ⟶ V) [(Under.post p).IsHomLift β φ]
    (ha : (Under.post p).obj a = U) (hb : (Under.post p).obj b = V) :
    p.IsHomLift β.right φ.right := by
  refine IsHomLift.of_fac p _ _ (congrArg Under.right ha) (congrArg Under.right hb) ?_
  have h2 := congrArg Under.Hom.right (IsHomLift.fac' (Under.post p) β φ)
  simp only [Under.comp_right, Under.eqToHom_right] at h2
  rw [show p.map φ.right = Under.Hom.right ((Under.post p).map φ) from rfl, h2]
  simp

/-- The canonical arrow of trivial deformations lies over the corresponding map of
square-zero extensions. -/
private theorem trivialTransition_isHomLift {V W : FGModuleCat.{u} k} (f : V ⟶ W) :
    p.IsHomLift (squareZeroOverMap k B S hS toS ((fgSiteModule B hk).map f))
      (trivialTransition B S hS toS hk p hp x₀ hx f).right := by
  let : (Under.post p : Under x₀ ⥤ Under (p.obj x₀)).IsFibered := underPost_isFibered p hp x₀
  have hinst : (Under.post p).IsHomLift
      (liftBaseOverMap k B S hS toS hk p x₀ hx ((fgSiteModule B hk).map f)).left
      (trivialTransition B S hS toS hk p hp x₀ hx f) :=
    Functor.pullbackFiberMap_isHomLift (Under.post p) (liftId k B S hS toS hk p x₀ hx)
      (liftBaseOverMap k B S hS toS hk p x₀ hx ((fgSiteModule B hk).map f))
  exact isHomLift_right_of_underPost B S hS p x₀
    (trivialTransition B S hS toS hk p hp x₀ hx f)
    (liftBaseOverMap k B S hS toS hk p x₀ hx ((fgSiteModule B hk).map f)).left
    (trivialLift B S hS toS hk p hp x₀ hx W).2 (trivialLift B S hS toS hk p hp x₀ hx V).2

/-- The trivial deformation over the trivial square-zero extension by `V`, read as an object
of the fibre of the predeformation category. -/
private abbrev trivialDeformationFib (V : FGModuleCat.{u} k) :
    Functor.Fiber (predeformationCategory iΛ (p ⋙ Over.post B.inclusion) x₀ hx₀).projection
      ((artinianSquareZeroExtensionFunctor Λ k).obj V) :=
  fromLiftFib B S hS iΛ toS hk p x₀ hx₀ hx V (trivialLift B S hS toS hk p hp x₀ hx V)

/-- The comparison of trivial deformations, read as a morphism of deformations of the
point. -/
private def trivialDeformationMorphism {V W : FGModuleCat.{u} k} (f : V ⟶ W) :
    DeformationMorphism iΛ (p ⋙ Over.post B.inclusion) x₀ hx₀
      (trivialDeformationFib B S hS iΛ toS hk p hp x₀ hx₀ hx V).1
      (trivialDeformationFib B S hS iΛ toS hk p hp x₀ hx₀ hx W).1 where
  ringHom := (artinianSquareZeroExtensionFunctor Λ k).map f
  arrow := (trivialTransition B S hS toS hk p hp x₀ hx f).right
  triangle := Under.w (trivialTransition B S hS toS hk p hp x₀ hx f)
  arrow_base := by
    have := trivialTransition_isHomLift B S hS toS hk p hp x₀ hx f
    exact liftTransition_arrow_base B S hS iΛ toS hk p x₀ hx₀ hx f
      (trivialLift B S hS toS hk p hp x₀ hx V) (trivialLift B S hS toS hk p hp x₀ hx W)
      (trivialTransition B S hS toS hk p hp x₀ hx f).right

/-- The comparison of trivial deformations lies over the corresponding map of square-zero
extensions. -/
private theorem trivialDeformationMorphism_isHomLift {V W : FGModuleCat.{u} k} (f : V ⟶ W) :
    (predeformationCategory iΛ (p ⋙ Over.post B.inclusion) x₀ hx₀).projection.IsHomLift
      ((artinianSquareZeroExtensionFunctor Λ k).map f)
      (trivialDeformationMorphism B S hS iΛ toS hk p hp x₀ hx₀ hx f :
        (trivialDeformationFib B S hS iΛ toS hk p hp x₀ hx₀ hx V).1 ⟶
          (trivialDeformationFib B S hS iΛ toS hk p hp x₀ hx₀ hx W).1) := by
  refine IsHomLift.of_fac' _ _ _
    (trivialDeformationFib B S hS iΛ toS hk p hp x₀ hx₀ hx V).2
    (trivialDeformationFib B S hS iΛ toS hk p hp x₀ hx₀ hx W).2 ?_
  rfl

/-- The structure arrow of the trivial deformation over the zero module is an isomorphism:
the square-zero immersion it lies over is one. -/
private theorem isIso_trivialLift_zero_hom :
    IsIso (trivialLift B S hS toS hk p hp x₀ hx (FGModuleCat.of k PUnit.{u + 1})).1.hom := by
  have h0 : IsIso (squareZeroArrow k B S hS toS hk
      ((fgSiteModule B hk).obj (FGModuleCat.of k PUnit.{u + 1}))) :=
    squareZeroArrow_zero_isIso k B S hS toS hk
  have hl := liftFiber_isHomLift B S hS toS hk p x₀ hx (FGModuleCat.of k PUnit.{u + 1})
    (trivialLift B S hS toS hk p hp x₀ hx (FGModuleCat.of k PUnit.{u + 1}))
  have := hp.isStronglyCartesian_homLift (squareZeroArrow k B S hS toS hk
      ((fgSiteModule B hk).obj (FGModuleCat.of k PUnit.{u + 1})))
    (trivialLift B S hS toS hk p hp x₀ hx (FGModuleCat.of k PUnit.{u + 1})).1.hom
  exact Functor.IsStronglyCartesian.isIso_of_base_isIso p
    (squareZeroArrow k B S hS toS hk
      ((fgSiteModule B hk).obj (FGModuleCat.of k PUnit.{u + 1})))
    (trivialLift B S hS toS hk p hp x₀ hx (FGModuleCat.of k PUnit.{u + 1})).1.hom

/-- Endomorphisms of the trivial deformation over `k[V]`, read in the fibre of the
predeformation category, are endomorphisms of the trivial lift of the point. -/
private def trivialEndEquiv (V : FGModuleCat.{u} k) :
    (trivialDeformationFib B S hS iΛ toS hk p hp x₀ hx₀ hx V ⟶
        trivialDeformationFib B S hS iΛ toS hk p hp x₀ hx₀ hx V) ≃
      (trivialLift B S hS toS hk p hp x₀ hx V ⟶ trivialLift B S hS toS hk p hp x₀ hx V) where
  toFun f :=
    toLiftMor B S hS iΛ toS hk p x₀ hx₀ hx V
      (trivialDeformationFib B S hS iΛ toS hk p hp x₀ hx₀ hx V).1
      (trivialDeformationFib B S hS iΛ toS hk p hp x₀ hx₀ hx V).1
      (trivialDeformationFib B S hS iΛ toS hk p hp x₀ hx₀ hx V).2
      (trivialDeformationFib B S hS iΛ toS hk p hp x₀ hx₀ hx V).2 f.1
      (fiberMor_ringHom B S hS iΛ p x₀ hx₀ _ _ f)
  invFun χ := fromLiftFibMor B S hS iΛ toS hk p x₀ hx₀ hx V χ
  left_inv f := by
    apply Functor.Fiber.hom_ext
    refine DeformationMorphism.ext_of_components iΛ (p ⋙ Over.post B.inclusion) x₀ hx₀ ?_ rfl
    exact (fiberMor_ringHom B S hS iΛ p x₀ hx₀ _ _ f).symm
  right_inv χ := by
    apply Functor.Fiber.hom_ext
    apply Under.UnderMorphism.ext
    rfl

/-- Two morphisms of deformations with the same arrow of `𝒞_Λ` agree as soon as the target
deformation presents the point itself. -/
private theorem deformationMorphism_ext_of_isIso_arrow
    {c d : (predeformationCategory iΛ (p ⋙ Over.post B.inclusion) x₀ hx₀).carrier}
    (m n : DeformationMorphism iΛ (p ⋙ Over.post B.inclusion) x₀ hx₀
      ((predeformationCategory iΛ (p ⋙ Over.post B.inclusion) x₀ hx₀).objects c)
      ((predeformationCategory iΛ (p ⋙ Over.post B.inclusion) x₀ hx₀).objects d))
    (hring : m.ringHom = n.ringHom)
    (hiso : IsIso ((predeformationCategory iΛ (p ⋙ Over.post B.inclusion) x₀ hx₀).objects
      d).arrow) : m = n := by
  refine DeformationMorphism.ext_of_components iΛ (p ⋙ Over.post B.inclusion) x₀ hx₀ hring ?_
  refine (cancel_epi ((predeformationCategory iΛ (p ⋙ Over.post B.inclusion) x₀
    hx₀).objects d).arrow).1 ?_
  rw [m.triangle, n.triangle]

/-- Every automorphism of the trivial dual-number deformation is infinitesimal: morphisms of
deformations commute with the arrows out of the point. -/
private theorem infinitesimalAutomorphismsAlongSplitPair_eq_top
    (hcof : IsCofiberedInGroupoids
      (predeformationCategory iΛ (p ⋙ Over.post B.inclusion) x₀ hx₀).projection) :
    infinitesimalAutomorphismsAlongSplitPair hcof (dualInclusion Λ k) (dualProjection Λ k)
      (dualInclusion_comp_dualProjection Λ k)
      (trivialDeformationMorphism B S hS iΛ toS hk p hp x₀ hx₀ hx
        (0 : FGModuleCat.of k PUnit.{u + 1} ⟶ FGModuleCat.of k k) :
        (trivialDeformationFib B S hS iΛ toS hk p hp x₀ hx₀ hx
            (FGModuleCat.of k PUnit.{u + 1})).1 ⟶
          (trivialDeformationFib B S hS iΛ toS hk p hp x₀ hx₀ hx (FGModuleCat.of k k)).1)
      (trivialDeformationMorphism_isHomLift B S hS iΛ toS hk p hp x₀ hx₀ hx 0) = ⊤ := by
  refine (Subgroup.eq_top_iff' _).2 fun a => ?_
  refine (mem_infinitesimalAutomorphismsAlongSplitPair_iff hcof (dualInclusion Λ k)
    (dualProjection Λ k) (dualInclusion_comp_dualProjection Λ k) _ _ a).2 ?_
  refine deformationMorphism_ext_of_isIso_arrow B S hS iΛ p x₀ hx₀ _ _ ?_
    (isIso_trivialLift_zero_hom B S hS toS hk p hp x₀ hx)
  show (a.asIso.hom.val : DeformationMorphism _ _ _ _ _ _).ringHom ≫ _ = _
  rw [fiberMor_ringHom B S hS iΛ p x₀ hx₀ _ _ a.asIso.hom]
  exact Category.id_comp _

/-- The comparison of endomorphisms turns composition of deformation morphisms into the
reversed composition of morphisms of lifts. -/
private theorem trivialEndEquiv_comp (V : FGModuleCat.{u} k)
    (f f' : trivialDeformationFib B S hS iΛ toS hk p hp x₀ hx₀ hx V ⟶
      trivialDeformationFib B S hS iΛ toS hk p hp x₀ hx₀ hx V) :
    trivialEndEquiv B S hS iΛ toS hk p hp x₀ hx₀ hx V (f ≫ f') =
      trivialEndEquiv B S hS iΛ toS hk p hp x₀ hx₀ hx V f' ≫
        trivialEndEquiv B S hS iΛ toS hk p hp x₀ hx₀ hx V f := by
  apply Functor.Fiber.hom_ext
  apply Under.UnderMorphism.ext
  rfl

/-- The comparison of endomorphisms preserves the identity. -/
private theorem trivialEndEquiv_id (V : FGModuleCat.{u} k) :
    trivialEndEquiv B S hS iΛ toS hk p hp x₀ hx₀ hx V
        (𝟙 (trivialDeformationFib B S hS iΛ toS hk p hp x₀ hx₀ hx V)) =
      𝟙 (trivialLift B S hS toS hk p hp x₀ hx V) := by
  apply Functor.Fiber.hom_ext
  apply Under.UnderMorphism.ext
  rfl

/-- Every endomorphism of a trivial deformation in the predeformation category is an
automorphism: it is one after the comparison with the lifts of the point. -/
private theorem isIso_trivialDeformationFib_end (V : FGModuleCat.{u} k)
    (f : trivialDeformationFib B S hS iΛ toS hk p hp x₀ hx₀ hx V ⟶
      trivialDeformationFib B S hS iΛ toS hk p hp x₀ hx₀ hx V) : IsIso f := by
  have hiso := isIso_infinitesimalAutomorphism k B S hS toS hk p x₀ hx hp
    ((fgSiteModule B hk).obj V)
    (trivialEndEquiv B S hS iΛ toS hk p hp x₀ hx₀ hx V f)
  refine ⟨(trivialEndEquiv B S hS iΛ toS hk p hp x₀ hx₀ hx V).symm
    (CategoryTheory.inv (trivialEndEquiv B S hS iΛ toS hk p hp x₀ hx₀ hx V f)), ?_, ?_⟩ <;>
  refine (trivialEndEquiv B S hS iΛ toS hk p hp x₀ hx₀ hx V).injective ?_ <;>
  rw [trivialEndEquiv_comp, Equiv.apply_symm_apply, trivialEndEquiv_id] <;> simp

/-- The automorphisms of a trivial deformation are all of its endomorphisms. -/
private def trivialAutEndEquiv (V : FGModuleCat.{u} k) :
    Aut (trivialDeformationFib B S hS iΛ toS hk p hp x₀ hx₀ hx V) ≃
      (trivialDeformationFib B S hS iΛ toS hk p hp x₀ hx₀ hx V ⟶
        trivialDeformationFib B S hS iΛ toS hk p hp x₀ hx₀ hx V) where
  toFun a := a.asIso.hom
  invFun f :=
    haveI := isIso_trivialDeformationFib_end B S hS iΛ toS hk p hp x₀ hx₀ hx V f
    .of (asIso f)
  left_inv _ := Aut.ext (Iso.ext rfl)
  right_inv _ := rfl


include hx₀ in
/-- **The trivial deformations over `k[V]` form a functor of `V`** over the square-zero
extension functor, and their fibre endomorphisms are the infinitesimal automorphisms of the
trivial lifts of `x₀` to `Spec k[V]`, compatibly with the transition maps. -/
public theorem exists_trivialDeformationFunctor_infinitesimalAutomorphisms :
    ∃ (Z : ∀ V : FGModuleCat.{u} k, Functor.Fiber
        (predeformationCategory iΛ (p ⋙ Over.post B.inclusion) x₀ hx₀).projection
          ((artinianSquareZeroExtensionFunctor Λ k).obj V))
      (τ : ∀ {V W : FGModuleCat.{u} k} (_ : V ⟶ W), (Z V).1 ⟶ (Z W).1)
      (ψ : ∀ V : FGModuleCat.{u} k, (Z V ⟶ Z V) ≃
        (infinitesimalAutomorphismSetFunctor k B S hS toS hk p x₀ hx hp).obj
          ((fgSiteModule B hk).obj V)),
      (∀ {V W : FGModuleCat.{u} k} (f : V ⟶ W),
        (predeformationCategory iΛ (p ⋙ Over.post B.inclusion) x₀ hx₀).projection.IsHomLift
          ((artinianSquareZeroExtensionFunctor Λ k).map f) (τ f)) ∧
      (∀ {V W Y : FGModuleCat.{u} k} (f : V ⟶ W) (g : W ⟶ Y), τ (f ≫ g) = τ f ≫ τ g) ∧
      ∀ {V W : FGModuleCat.{u} k} (f : V ⟶ W) (θ : Z V ⟶ Z V) (θ' : Z W ⟶ Z W),
        τ f ≫ θ'.1 = θ.1 ≫ τ f →
          ψ W θ' = (infinitesimalAutomorphismSetFunctor k B S hS toS hk p x₀ hx hp).map
            ((fgSiteModule B hk).map f) (ψ V θ) := by
  let : (Under.post p : Under x₀ ⥤ Under (p.obj x₀)).IsFibered := underPost_isFibered p hp x₀
  refine ⟨fun V => trivialDeformationFib B S hS iΛ toS hk p hp x₀ hx₀ hx V,
    fun f => trivialDeformationMorphism B S hS iΛ toS hk p hp x₀ hx₀ hx f,
    fun V => trivialEndEquiv B S hS iΛ toS hk p hp x₀ hx₀ hx V,
    fun f => trivialDeformationMorphism_isHomLift B S hS iΛ toS hk p hp x₀ hx₀ hx f, ?_, ?_⟩
  · intro V W Y f g
    refine DeformationMorphism.ext_of_components iΛ (p ⋙ Over.post B.inclusion) x₀ hx₀
      ((artinianSquareZeroExtensionFunctor Λ k).map_comp f g) ?_
    have hbase : liftBaseOverMap k B S hS toS hk p x₀ hx ((fgSiteModule B hk).map (f ≫ g)) =
        liftBaseOverMap k B S hS toS hk p x₀ hx ((fgSiteModule B hk).map g) ≫
          liftBaseOverMap k B S hS toS hk p x₀ hx ((fgSiteModule B hk).map f) := by
      apply Over.OverMorphism.ext
      rw [Functor.map_comp]
      exact liftBaseThickeningMap_comp k B S hS toS hk p x₀ hx _ _
    show (Functor.pullbackFiberMap (Under.post p) (liftId k B S hS toS hk p x₀ hx)
        (liftBaseOverMap k B S hS toS hk p x₀ hx ((fgSiteModule B hk).map (f ≫ g)))).right =
      (trivialTransition B S hS toS hk p hp x₀ hx g).right ≫
        (trivialTransition B S hS toS hk p hp x₀ hx f).right
    rw [hbase, ← Functor.pullbackFiberMap_comp]
    rfl
  · intro V W f θ θ' h
    rw [infinitesimalAutomorphismSetFunctor_map]
    apply fiberEndRestrict_eq
    apply Under.UnderMorphism.ext
    exact congrArg (fun m : DeformationMorphism iΛ (p ⋙ Over.post B.inclusion) x₀ hx₀ _ _ =>
      m.arrow) h

variable (hRS : SatisfiesRSStar B S hS p hp)

/-- The infinitesimal automorphisms of the trivial dual-number deformation of the point are
the value of the linear functor `Inf_{x₀}` at the rank-one vector space. -/
private def infinitesimalComparison
    (hcof : IsCofiberedInGroupoids
      (predeformationCategory iΛ (p ⋙ Over.post B.inclusion) x₀ hx₀).projection) :
    ↥(infinitesimalAutomorphismsAlongSplitPair hcof (dualInclusion Λ k) (dualProjection Λ k)
        (dualInclusion_comp_dualProjection Λ k)
        (trivialDeformationMorphism B S hS iΛ toS hk p hp x₀ hx₀ hx
          (0 : FGModuleCat.of k PUnit.{u + 1} ⟶ FGModuleCat.of k k) :
          (trivialDeformationFib B S hS iΛ toS hk p hp x₀ hx₀ hx
              (FGModuleCat.of k PUnit.{u + 1})).1 ⟶
            (trivialDeformationFib B S hS iΛ toS hk p hp x₀ hx₀ hx (FGModuleCat.of k k)).1)
        (trivialDeformationMorphism_isHomLift B S hS iΛ toS hk p hp x₀ hx₀ hx 0)) ≃
      ((infinitesimalAutomorphismFunctor k B S hS toS hk p x₀ hx hp hRS).functor.obj
        ((fgSiteModule B hk).obj (FGModuleCat.of k k)) : Type w) :=
  (((MulEquiv.subgroupCongr (infinitesimalAutomorphismsAlongSplitPair_eq_top B S hS iΛ toS hk
          p hp x₀ hx₀ hx hcof)).trans Subgroup.topEquiv).toEquiv.trans
      ((trivialAutEndEquiv B S hS iΛ toS hk p hp x₀ hx₀ hx (FGModuleCat.of k k)).trans
        (trivialEndEquiv B S hS iΛ toS hk p hp x₀ hx₀ hx (FGModuleCat.of k k)))).trans
    ((infinitesimalAutomorphismFunctor k B S hS toS hk p x₀ hx hp hRS).autEquiv
      ((fgSiteModule B hk).obj (FGModuleCat.of k k))).symm

/-- The comparison carries an infinitesimal automorphism to the endomorphism of the trivial
deformation given by the same arrow of the fibred category. -/
private theorem infinitesimalComparison_arrow
    (hcof : IsCofiberedInGroupoids
      (predeformationCategory iΛ (p ⋙ Over.post B.inclusion) x₀ hx₀).projection)
    (a : ↥(infinitesimalAutomorphismsAlongSplitPair hcof (dualInclusion Λ k)
      (dualProjection Λ k) (dualInclusion_comp_dualProjection Λ k)
      (trivialDeformationMorphism B S hS iΛ toS hk p hp x₀ hx₀ hx
        (0 : FGModuleCat.of k PUnit.{u + 1} ⟶ FGModuleCat.of k k) :
        (trivialDeformationFib B S hS iΛ toS hk p hp x₀ hx₀ hx
            (FGModuleCat.of k PUnit.{u + 1})).1 ⟶
          (trivialDeformationFib B S hS iΛ toS hk p hp x₀ hx₀ hx (FGModuleCat.of k k)).1)
      (trivialDeformationMorphism_isHomLift B S hS iΛ toS hk p hp x₀ hx₀ hx 0))) :
    (((infinitesimalAutomorphismFunctor k B S hS toS hk p x₀ hx hp hRS).autEquiv
          ((fgSiteModule B hk).obj (FGModuleCat.of k k))
        (infinitesimalComparison B S hS iΛ toS hk p hp x₀ hx₀ hx hRS hcof a)).1).right =
      (a.val.asIso.hom.val :
        DeformationMorphism iΛ (p ⋙ Over.post B.inclusion) x₀ hx₀ _ _).arrow := by
  show (((infinitesimalAutomorphismFunctor k B S hS toS hk p x₀ hx hp hRS).autEquiv _)
    (((infinitesimalAutomorphismFunctor k B S hS toS hk p x₀ hx hp hRS).autEquiv _).symm
      (trivialEndEquiv B S hS iΛ toS hk p hp x₀ hx₀ hx (FGModuleCat.of k k)
        a.val.asIso.hom)) |>.1).right = _
  rw [Equiv.apply_symm_apply]
  rfl

/-- **Stacks Project, Tag 0D18, infinitesimal automorphisms.** For a category fibred in
groupoids over the big fppf site of a locally Noetherian scheme satisfying (RS*), the
infinitesimal automorphisms of the deformation category of a finite-type field-valued point
are the value of the infinitesimal automorphism functor of Tag 07Y9 at the rank-one vector
space, by a `k`-linear equivalence carrying an automorphism to the endomorphism of the
trivial deformation given by the same arrow. -/
@[stacks 0D18 "infinitesimal automorphisms"]
public theorem infinitesimalAutomorphisms_deformationCategory_linearEquiv
    (B : BigFppfSite.{u}) (S : Scheme.{u}) [IsLocallyNoetherian S] (hS : B.Contains S)
    {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
    (iΛ : Spec (.of Λ) ⟶ S) (toS : Spec (.of k) ⟶ S)
    (hk : B.Contains (Spec (.of k)))
    (hfin : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
    (hqc : QuasiCompact (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
    {X : Type v} [Category.{w} X] (p : X ⥤ BigFppfOver B S hS)
    (hp : p.IsFiberedInGroupoids) (hRS : SatisfiesRSStar B S hS p hp) (x₀ : X)
    (hx₀ : (p ⋙ Over.post B.inclusion).obj x₀ =
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
    (hx : p.obj x₀ = algebraOver k B S hS toS hk) :
    let D := predeformationCategory iΛ (p ⋙ Over.post B.inclusion) x₀ hx₀
    let hD : Deformation.IsDeformationCategory D.projection :=
      isDeformationCategory_predeformationCategory_of_satisfiesRSStar B S hS p hp hRS iΛ x₀
        hx₀ hfin hqc
    let A₀ := (artinianSquareZeroExtensionFunctor Λ k).obj (FGModuleCat.of k PUnit.{u + 1})
    let Aε := (artinianSquareZeroExtensionFunctor Λ k).obj (FGModuleCat.of k k)
    let g : A₀ ⟶ Aε := (artinianSquareZeroExtensionFunctor Λ k).map 0
    let e : Aε ⟶ A₀ := (artinianSquareZeroExtensionFunctor Λ k).map 0
    let M : SiteModule k B := (fgSiteModule B hk).obj (FGModuleCat.of k k)
    let L := infinitesimalAutomorphismFunctor k B S hS toS hk p x₀ hx hp hRS
    let t := trivialDeformation k B S hS toS hk p x₀ hx hp M
    ∃ (hge : g ≫ e = 𝟙 A₀) (z₀ : D.projection.Fiber A₀) (zε : D.projection.Fiber Aε)
      (i : z₀.1 ⟶ zε.1) (hi : D.projection.IsHomLift g i)
      (η : (D.objects zε.1).point ≅ t.1.right),
      let G := ↥(infinitesimalAutomorphismsAlongSplitPair hD.predeformation.cofibered g e hge
        i hi)
      (D.objects zε.1).arrow ≫ η.hom = t.1.hom ∧
        ∃ hA : AddCommGroup G,
          letI : AddCommGroup G := hA
          ∃ hM : Module k G,
            letI : Module k G := hM
            ∃ E : G ≃ₗ[k] (L.functor.obj M : Type w),
              ∀ a : G, (L.autEquiv M (E a)).1.right =
                η.inv ≫ (D.morphisms zε.1 zε.1 a.val.asIso.hom.val).arrow ≫ η.hom := by
  intro D hD A₀ Aε g e M L t
  refine ⟨dualInclusion_comp_dualProjection Λ k,
    trivialDeformationFib B S hS iΛ toS hk p hp x₀ hx₀ hx (FGModuleCat.of k PUnit.{u + 1}),
    trivialDeformationFib B S hS iΛ toS hk p hp x₀ hx₀ hx (FGModuleCat.of k k),
    trivialDeformationMorphism B S hS iΛ toS hk p hp x₀ hx₀ hx 0,
    trivialDeformationMorphism_isHomLift B S hS iΛ toS hk p hp x₀ hx₀ hx 0, ?_, ?_⟩
  · exact Iso.refl _
  refine ⟨?_, ?_⟩
  · rw [Iso.refl_hom]
    exact Category.comp_id _
  let eqv := infinitesimalComparison B S hS iΛ toS hk p hp x₀ hx₀ hx hRS
    hD.predeformation.cofibered
  let A := eqv.addCommGroup
  let eadd := { toEquiv := eqv, map_add' := fun x y => eqv.apply_symm_apply _ :
    _ ≃+ (L.functor.obj M : Type w) }
  let Mo := eadd.module k
  refine ⟨A, Mo, eadd.linearEquiv k, fun a => ?_⟩
  exact (infinitesimalComparison_arrow B S hS iΛ toS hk p hp x₀ hx₀ hx hRS
    hD.predeformation.cofibered a).trans ((Category.comp_id _).symm.trans (Category.id_comp _).symm)

end InfinitesimalComparison

end Deformation.Artin

end
