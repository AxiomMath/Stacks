module

public import Mathlib.Algebra.Exact.Basic
public import Mathlib.LinearAlgebra.Prod
public import StacksFrontier.Deformation.Artin.Infinitesimal
public import StacksFrontier.Deformation.Artin.Infinitesimal.AutomorphismFunctor
public import StacksFrontier.Deformation.ArtinCriteria.RimSchlessinger

/-!
# Functoriality of the infinitesimal invariants, and the six-term sequence of a 2-fibre product

Let `𝒳` and `𝒴` be categories fibred in groupoids over the big fppf site of a scheme `S`, let
`F : 𝒳 ⥤ 𝒴` be a `1`-morphism over that site, let `A` be an `S`-algebra whose spectrum lies in
the site, and let `x` be an object of `𝒳` over `Spec A`.  For an `A`-module `M` the source's
Remark 07YA asserts that `F` induces `A`-linear maps

`T_x(M) ⟶ T_{F x}(M)` and `Inf_x(M) ⟶ Inf_{F x}(M)`

on the functors of Stacks 07Y9.  Those functors are *chosen* objects, produced from an
existence statement by `Deformation.Artin.tangentFunctor` and
`Deformation.Artin.infinitesimalAutomorphismFunctor`, and the only handle on their values is
the family of bijections with lift classes carried by
`Deformation.Artin.TangentFunctorData` and
`Deformation.Artin.InfinitesimalAutomorphismFunctorData`.  This file builds the maps through
those bijections: nothing here chooses data from an existence statement, and the maps are
constructed, not selected.

## Main definitions

* `Deformation.Artin.fiberOfComp`: the functor `(G ⋙ r).Fiber T ⥤ r.Fiber T` induced by a
  functor over the base.
* `Deformation.Artin.underFiberPost`: the functor on lifts of `x` under an arrow `a` of the
  base induced by a `1`-morphism — a lift `x ⟶ x'` of `x` is carried to the lift
  `F x ⟶ F x'` of `F x`.  Its source and target are `Deformation.Artin.LiftOut p a x hx` and
  `Deformation.Artin.LiftOut q a (F x) hFx`, so this is the special case of the source's Lemma
  07Y7, `Deformation.Artin.liftOutFunctorOfPullback`, in which the commutative square of the base
  is the identity square at `a` and `y` is `F x` itself; stated directly, it needs no choice of
  pullbacks and the comparison arrow is an identity.
* `Deformation.Artin.liftClassOfOneMorphism`: the induced map on the isomorphism classes of
  lifts over the trivial square-zero extension `A[M]`.
* `Deformation.Artin.tangentMapOfOneMorphism`: the map `T_x(M) ⟶ T_{F x}(M)`, read through the
  two `liftEquiv` bijections.
* `Deformation.Artin.trivialComparison`, `Deformation.Artin.trivialComparisonHom`: the
  comparison arrow between the trivial deformation of `F x` and the image under `F` of the
  trivial deformation of `x`, in `𝒴` and as a morphism of lifts.
* `Deformation.Artin.infMapOfOneMorphism`: the map `Inf_x(M) ⟶ Inf_{F x}(M)`, the image under
  `F` of an infinitesimal automorphism conjugated by that comparison.
* `Deformation.Artin.squareZeroLiftPostArrow`: the image under a `1`-morphism of an arrow of
  lifts, ascribed the type the induced functor on fibres of lifts gives its objects.
* `Deformation.Artin.infFunctorMapOfOneMorphism`,
  `Deformation.Artin.infLinearMapOfOneMorphism`: the map `Inf_x(M) ⟶ Inf_{F x}(M)` read through
  the two `autEquiv` bijections, and the same map packaged as an `A`-linear map.
* `Deformation.Artin.TwoFibreSixTermTail`: the four assertions of Stacks 0DNN that this file
  carries rather than proves, as one `Prop`.
* `Deformation.Artin.liftBaseInclusion`, `Deformation.Artin.liftIdToTrivial`: the square-zero
  immersion and the structure arrow of the trivial deformation, read as arrows of base
  thickenings and of lifts out of `x` itself.

## Main results

* `Deformation.Artin.isPullbackOfSquareZeroLift_unique`: a lift class determines its pullback
  along a module map.  This is what turns the *relational* naturality field
  `TangentFunctorData.liftEquiv_natural` into an equation, and so the whole of the `T`-side
  naturality rests on it.
* `Deformation.Artin.tangentMapOfOneMorphism_natural`: the tangent map is natural in `M`.
* `Deformation.Artin.isLinearMap_tangentMapOfOneMorphism`,
  `Deformation.Artin.tangentLinearMapOfOneMorphism`: the tangent map is `A`-linear, and the
  same map packaged as an `A`-linear map.
* `Deformation.Artin.infMapOfOneMorphism_fac`,
  `Deformation.Artin.trivialComparisonHom_naturality`,
  `Deformation.Artin.map_trivialTransitionUnder_isHomLift`: the squares that the naturality of
  the `Inf`-side map in `M` reduces to.
* `Deformation.Artin.squareZeroLiftPost_map_fiberEndRestrict`: a `1`-morphism commutes with
  restriction of endomorphisms of lifts.  This is the identity the `Inf`-side naturality rests
  on, the counterpart of `isPullbackOfSquareZeroLift_unique` on the `T`-side.
* `Deformation.Artin.infMapOfOneMorphism_natural`,
  `Deformation.Artin.infFunctorMapOfOneMorphism_natural`,
  `Deformation.Artin.isLinearMap_infFunctorMapOfOneMorphism`: the `Inf`-side map is natural in
  `M` and `A`-linear.
* `Deformation.Artin.autEquiv_zero`, `Deformation.Artin.liftEquiv_zero`: the zero of
  `Inf_x(M)` is the identity automorphism of the trivial deformation, and the zero of `T_x(M)`
  is the isomorphism class of the trivial deformation.  Both come from
  `Deformation.Artin.squareZeroOverMap_zero`: the map of trivial square-zero extensions induced
  by the zero module map factors through `Spec A`, so the transition map along it restricts
  endomorphisms through the lift `x` of itself, which has none but the identity.
* `Deformation.Artin.injective_twoFibreInfProj`: exactness of the six-term sequence of Stacks
  0DNN at `Inf_w(M)`, i.e. the injectivity of `Inf_w(M) ⟶ Inf_x(M) ⊕ Inf_z(M)`.
* `Deformation.Artin.injective_twoFibreInfProj`: Stacks 0DNN, exactness at `Inf_w(M)`.

## Implementation notes

`A`-linearity is **not** Tag 06I7 (`Deformation.fgModuleCat_linearFunctorLift_natTrans`).  That
statement is about the *canonical* linear lift `Deformation.fgModuleCatLinearFunctorLift` of a
set-valued functor on `FGModuleCat`, and it concludes that a natural transformation of the
set-valued functors lifts; here the source category is `Deformation.Artin.SiteModule A B`, the
two linear functors are arbitrary members of `TangentFunctorData` / of
`InfinitesimalAutomorphismFunctorData` rather than the canonical lifts (the chosen ones are
`Classical.choice`, so they are not provably the canonical lift of anything), and on the
tangent side they take values in two different type universes.  So linearity is proved here
from scratch, by `Deformation.Artin.isLinearMap_of_natural_split`: a natural family of maps
between the values of two linear functors is linear at every object admitting a split square,
which is the argument of 06I7 with the biproduct replaced by an explicitly supplied pair of
sections and retractions.  `Deformation.Artin.siteModuleInl`,
`Deformation.Artin.siteModuleInr` supply that square in `SiteModule A B`.

`Deformation.Artin.underFiber_isHomLift` duplicates the private `liftFiber_isHomLift` of
`StacksFrontier.Deformation.Artin.Infinitesimal.AutomorphismFunctor`, which is not exported.

The image of an arrow of lifts under a `1`-morphism has two spellings: `(Under.post F).map ρ`,
and the arrow between the objects that `Deformation.Artin.squareZeroLiftPost` assigns.  They
are definitionally equal but are not unified at reducible transparency, which is why
`Deformation.Artin.squareZeroLiftPostArrow` ascribes the second type to the first term and the
statements about restriction of endomorphisms are made at that spelling; crossing between the
two is then always done by a term-mode application, never by rewriting.

Stacks 0DNN is stated here only in part.  The two `𝒵`-side comparison maps into the `𝒴`-term
are the maps induced by `q` followed by the transport of `Inf` and of `T` along the comparison
isomorphism `w.iso` of the object of the `2`-fibre product; that transport is the content of
the sections `TransportTangent` and `TransportInf` below, but the two composites, the boundary
map `δ` and the four exactness assertions that mention them are not assembled here.  They are
explicit named hypotheses of `Deformation.Artin.injective_twoFibreInfProj`, with the
obligations collected in `Deformation.Artin.TwoFibreSixTermTail`; what the theorem itself
proves is the first exactness assertion, at `Inf_w(M)`.  The whole sequence is
`Deformation.Artin.twoFibre_sixTermExact` in
`StacksFrontier.Deformation.Artin.Infinitesimal.TwoFibreInfExact`.

## References

* [Stacks Project, Tag 07Y7](https://stacks.math.columbia.edu/tag/07Y7)
* [Stacks Project, Tag 07YA](https://stacks.math.columbia.edu/tag/07YA)
* [Stacks Project, Tag 0DNN](https://stacks.math.columbia.edu/tag/0DNN)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

attribute [local implicit_reducible] CategoryTheory.Functor.Fiber
  CategoryTheory.Functor.Fiber.fiberInclusion
  CategoryTheory.Functor.ChoiceOfPullbacks.pullbackFunctor
  CategoryTheory.Under.post

namespace Deformation.Artin

/-! ### Fibres along a composite -/

section FiberComp
open Functor
universe u₁ v₁ u₂ v₂ u₃ v₃

variable {𝒮 : Type u₁} [Category.{v₁} 𝒮] {𝒳 : Type u₂} [Category.{v₂} 𝒳]
  {𝒴 : Type u₃} [Category.{v₃} 𝒴]

/-- An arrow lifting `f` through a composite has image lifting `f` through the second
factor. -/
public theorem isHomLift_map_of_comp (G : 𝒳 ⥤ 𝒴) (r : 𝒴 ⥤ 𝒮) {R S : 𝒮} {a b : 𝒳}
    (f : R ⟶ S) (φ : a ⟶ b) (h : (G ⋙ r).IsHomLift f φ) : r.IsHomLift f (G.map φ) := by
  obtain ⟨⟩ := h
  exact IsHomLift.map r (G.map φ)

/-- The functor on fibres induced by a functor over the base. -/
public def fiberOfComp (G : 𝒳 ⥤ 𝒴) (r : 𝒴 ⥤ 𝒮) (T : 𝒮) :
    (G ⋙ r).Fiber T ⥤ r.Fiber T where
  obj t := ⟨G.obj t.1, t.2⟩
  map m := ⟨G.map m.1, isHomLift_map_of_comp G r _ _ m.2⟩
  map_id t := Functor.Fiber.hom_ext (G.map_id t.1)
  map_comp m n := Functor.Fiber.hom_ext (G.map_comp m.1 n.1)

end FiberComp

/-! ### Lifts under an object and the functor induced on them -/

section UnderFiber
open Functor
universe u₁ v₁ u₂ v₂ u₃ v₃

variable {C : Type u₁} [Category.{v₁} C] {X : Type u₂} [Category.{v₂} X]
  {Y : Type u₃} [Category.{v₃} Y]

/-- The codomain of a lift of `x` under `a : U ⟶ V` lies over `V`. -/
public theorem underFiber_right_obj (p : X ⥤ C) {U V : C} {x : X} (hx : p.obj x = U)
    (a : U ⟶ V) (t : (Under.post p).Fiber (Under.mk (eqToHom hx ≫ a))) :
    p.obj t.1.right = V :=
  congrArg Under.right t.2

/-- The structure arrow of a lift of `x` under `a` lies over `a`.

This duplicates the private `liftFiber_isHomLift` of
`StacksFrontier.Deformation.Artin.Infinitesimal.AutomorphismFunctor`. -/
public theorem underFiber_isHomLift (p : X ⥤ C) {U V : C} {x : X} (hx : p.obj x = U)
    (a : U ⟶ V) (t : (Under.post p).Fiber (Under.mk (eqToHom hx ≫ a))) :
    p.IsHomLift a t.1.hom := by
  apply IsHomLift.of_fac p a t.1.hom hx (underFiber_right_obj p hx a t)
  have hw := Under.w (eqToHom t.2)
  simp only [Under.eqToHom_right] at hw
  change p.map t.1.hom ≫ eqToHom (underFiber_right_obj p hx a t) = eqToHom hx ≫ a at hw
  rw [hw]
  simp

/-- A vertical arrow between the codomains of two lifts of `x` compatible with the structure
arrows is a morphism of lifts. -/
public def underFiberHomMk (p : X ⥤ C) {U V : C} {x : X} (hx : p.obj x = U) (a : U ⟶ V)
    {s t : (Under.post p).Fiber (Under.mk (eqToHom hx ≫ a))}
    (χ : s.1.right ⟶ t.1.right) (hχ : p.IsHomLift (𝟙 V) χ)
    (hw : s.1.hom ≫ χ = t.1.hom) : s ⟶ t := by
  refine ⟨Under.homMk χ hw, ?_⟩
  refine IsHomLift.of_fac' (Under.post p) (𝟙 _) _ s.2 t.2 ?_
  apply Under.UnderMorphism.ext
  have := hχ
  simp only [Under.comp_right, Under.eqToHom_right, Under.id_right, Under.post_map,
    Under.homMk_right]
  rw [IsHomLift.fac' p (𝟙 V) χ]
  simp

@[simp]
public theorem underFiberHomMk_right (p : X ⥤ C) {U V : C} {x : X} (hx : p.obj x = U)
    (a : U ⟶ V) {s t : (Under.post p).Fiber (Under.mk (eqToHom hx ≫ a))}
    (χ : s.1.right ⟶ t.1.right) (hχ : p.IsHomLift (𝟙 V) χ)
    (hw : s.1.hom ≫ χ = t.1.hom) :
    (underFiberHomMk p hx a χ hχ hw).1.right = χ := rfl

/-- The image under a `1`-morphism of a lift of `x` under `a` is a lift of `F x` under `a`. -/
public theorem underPost_map_mem_fiber (p : X ⥤ C) (q : Y ⥤ C) (F : X ⥤ Y) (hF : F ⋙ q = p)
    {U V : C} {x : X} (hx : p.obj x = U) (hFx : q.obj (F.obj x) = U) (a : U ⟶ V)
    (t : (Under.post p).Fiber (Under.mk (eqToHom hx ≫ a))) :
    (Under.post q).obj ((Under.post F).obj t.1) =
      Under.mk (eqToHom hFx ≫ a) := by
  have hlift : q.IsHomLift a (F.map t.1.hom) :=
    lift_map_isHomLift p q F hF a hx (underFiber_right_obj p hx a t) t.1.hom
      (underFiber_isHomLift p hx a t)
  refine StructuredArrow.obj_ext _ _ (IsHomLift.codomain_eq q a (F.map t.1.hom)) ?_
  show q.map (F.map t.1.hom) ≫ eqToHom (IsHomLift.codomain_eq q a (F.map t.1.hom)) =
    eqToHom hFx ≫ a
  rw [IsHomLift.fac' q a (F.map t.1.hom)]
  simp

/-- A `1`-morphism of categories over the base carries lifts of `x` under `a` to lifts of
`F x` under `a`.  This is `Deformation.Artin.liftOutFunctorOfPullback`, the source's Lemma 07Y7,
for the identity square at `a` and for `y = F x`, where no pullback has to be chosen. -/
public def underFiberPost (p : X ⥤ C) (q : Y ⥤ C) (F : X ⥤ Y) (hF : F ⋙ q = p)
    {U V : C} {x : X} (hx : p.obj x = U) (hFx : q.obj (F.obj x) = U) (a : U ⟶ V) :
    (Under.post p).Fiber (Under.mk (eqToHom hx ≫ a)) ⥤
      (Under.post q).Fiber (Under.mk (eqToHom hFx ≫ a)) where
  obj t := ⟨(Under.post F).obj t.1, underPost_map_mem_fiber p q F hF hx hFx a t⟩
  map {s t} m := ⟨(Under.post F).map m.1, by
    have hs : p.obj s.1.right = V := underFiber_right_obj p hx a s
    have ht : p.obj t.1.right = V := underFiber_right_obj p hx a t
    have h₀ : p.IsHomLift (𝟙 V) m.1.right :=
      underPost_isHomLift_right p (𝟙 (Under.mk (eqToHom hx ≫ a))) m.1 m.2
    have h₁ : q.IsHomLift (𝟙 V) (F.map m.1.right) :=
      lift_map_isHomLift p q F hF (𝟙 V) hs ht m.1.right h₀
    refine IsHomLift.of_fac' (Under.post q) (𝟙 _) _
      (underPost_map_mem_fiber p q F hF hx hFx a s)
      (underPost_map_mem_fiber p q F hF hx hFx a t) ?_
    apply Under.UnderMorphism.ext
    simp only [Under.comp_right, Under.eqToHom_right, Under.id_right, Under.post_map,
      Under.homMk_right]
    rw [IsHomLift.fac' q (𝟙 V) (F.map m.1.right)]
    simp⟩
  map_id t := Functor.Fiber.hom_ext ((Under.post F).map_id t.1)
  map_comp m n := Functor.Fiber.hom_ext ((Under.post F).map_comp m.1 n.1)

@[simp]
public theorem underFiberPost_obj (p : X ⥤ C) (q : Y ⥤ C) (F : X ⥤ Y) (hF : F ⋙ q = p)
    {U V : C} {x : X} (hx : p.obj x = U) (hFx : q.obj (F.obj x) = U) (a : U ⟶ V)
    (t : (Under.post p).Fiber (Under.mk (eqToHom hx ≫ a))) :
    ((underFiberPost p q F hF hx hFx a).obj t).1 = (Under.post F).obj t.1 := rfl

@[simp]
public theorem underFiberPost_map (p : X ⥤ C) (q : Y ⥤ C) (F : X ⥤ Y) (hF : F ⋙ q = p)
    {U V : C} {x : X} (hx : p.obj x = U) (hFx : q.obj (F.obj x) = U) (a : U ⟶ V)
    {s t : (Under.post p).Fiber (Under.mk (eqToHom hx ≫ a))} (m : s ⟶ t) :
    ((underFiberPost p q F hF hx hFx a).map m).1 = (Under.post F).map m.1 := rfl

/-- The image under a `1`-morphism of an arrow of lifts lying over an arrow of base
thickenings lies over the corresponding arrow of base thickenings. -/
public theorem underPost_map_isHomLift (p : X ⥤ C) (q : Y ⥤ C) (F : X ⥤ Y) (hF : F ⋙ q = p)
    {U V W : C} {x : X} (hx : p.obj x = U) (hFx : q.obj (F.obj x) = U)
    (a : U ⟶ V) (a' : U ⟶ W) (g : V ⟶ W)
    (hcomm : (eqToHom hFx ≫ a) ≫ g = eqToHom hFx ≫ a')
    (s : (Under.post p).Fiber (Under.mk (eqToHom hx ≫ a)))
    (t : (Under.post p).Fiber (Under.mk (eqToHom hx ≫ a')))
    (m : s.1 ⟶ t.1) (hm : p.IsHomLift g m.right) :
    (Under.post q).IsHomLift
      (Under.homMk g hcomm :
        (Under.mk (eqToHom hFx ≫ a) : Under (q.obj (F.obj x))) ⟶ Under.mk (eqToHom hFx ≫ a'))
      ((Under.post F).map m) := by
  have h1 : q.IsHomLift g (F.map m.right) :=
    lift_map_isHomLift p q F hF g (underFiber_right_obj p hx a s)
      (underFiber_right_obj p hx a' t) m.right hm
  refine IsHomLift.of_fac' (Under.post q) _ _
    (underPost_map_mem_fiber p q F hF hx hFx a s)
    (underPost_map_mem_fiber p q F hF hx hFx a' t) ?_
  apply Under.UnderMorphism.ext
  simp only [Under.comp_right, Under.eqToHom_right, Under.post_map, Under.homMk_right]
  rw [IsHomLift.fac' q g (F.map m.right)]

end UnderFiber

/-! ### Linearity from naturality over a split square -/

section Linearity
open CategoryTheory
universe uR uD vD z₁ z₂

/-- A natural family of maps between the values of two linear functors is linear at every
object carrying a split square.  This is the argument of Tag 06I7 with the biproduct replaced
by an explicitly supplied pair of sections and retractions, which is what makes it applicable
to a source category that is not `FGModuleCat` and to two functors with values in different
type universes. -/
public theorem isLinearMap_of_natural_split (R : Type uR) [CommRing R]
    {D : Type uD} [Category.{vD} D] [Preadditive D] [CategoryTheory.Linear R D]
    (Fu : D ⥤ ModuleCat.{z₁} R) (Gu : D ⥤ ModuleCat.{z₂} R)
    [Fu.Additive] [Gu.Additive] [Fu.Linear R] [Gu.Linear R]
    (t : ∀ Z, Fu.obj Z → Gu.obj Z)
    (ht : ∀ {Z W : D} (g : Z ⟶ W) (z : Fu.obj Z), t W ((Fu.map g) z) = (Gu.map g) (t Z z))
    (E E' : D) (p₁ p₂ : E' ⟶ E) (i₁ i₂ : E ⟶ E')
    (h₁₁ : i₁ ≫ p₁ = 𝟙 E) (h₂₂ : i₂ ≫ p₂ = 𝟙 E)
    (h₁₂ : i₂ ≫ p₁ = 0) (h₂₁ : i₁ ≫ p₂ = 0) :
    IsLinearMap R (t E) := by
  constructor
  · intro u v
    let z : Fu.obj E' := (Fu.map i₁) u + (Fu.map i₂) v
    have e (i : E ⟶ E') (q : E' ⟶ E) (w : Fu.obj E) :
        (Fu.map q) ((Fu.map i) w) = (Fu.map (i ≫ q)) w := by simp
    have hF₁ : (Fu.map p₁) z = u := by
      show (Fu.map p₁) ((Fu.map i₁) u + (Fu.map i₂) v) = u
      rw [map_add, e, e, h₁₁, h₁₂]
      simp
    have hF₂ : (Fu.map p₂) z = v := by
      show (Fu.map p₂) ((Fu.map i₁) u + (Fu.map i₂) v) = v
      rw [map_add, e, e, h₂₁, h₂₂]
      simp
    have hFadd : (Fu.map (p₁ + p₂)) z = u + v := by
      rw [Fu.map_add]
      show (Fu.map p₁) z + (Fu.map p₂) z = u + v
      rw [hF₁, hF₂]
    have hGadd (b : Gu.obj E') : (Gu.map (p₁ + p₂)) b = (Gu.map p₁) b + (Gu.map p₂) b := by
      rw [Gu.map_add]
      rfl
    calc
      _ = t E ((Fu.map (p₁ + p₂)) z) := by rw [hFadd]
      _ = (Gu.map (p₁ + p₂)) (t E' z) := ht (p₁ + p₂) z
      _ = (Gu.map p₁) (t E' z) + (Gu.map p₂) (t E' z) := hGadd _
      _ = t E u + t E v := by rw [← ht p₁ z, ← ht p₂ z, hF₁, hF₂]
  · intro r u
    let g : E ⟶ E := r • (𝟙 E)
    have hFsmul : (Fu.map g) u = r • u := by simp [g]
    have hGsmul (b : Gu.obj E) : (Gu.map g) b = r • b := by simp [g]
    calc
      _ = t E ((Fu.map g) u) := by rw [hFsmul]
      _ = (Gu.map g) (t E u) := ht g u
      _ = _ := hGsmul _

end Linearity

/-! ### The split square of a site module -/

section SiteModuleSplit
universe u z₁ z₂

variable (A : Type u) [CommRing A] (B : BigFppfSite.{u})
  (hA : B.Contains (Spec (.of A)))

/-- The first inclusion into a product of site modules. -/
public def siteModuleInl (M N : SiteModule A B) : M ⟶ siteModuleProd A B hA M N :=
  ObjectProperty.homMk (ModuleCat.ofHom (LinearMap.inl A M.obj N.obj))

/-- The second inclusion into a product of site modules. -/
public def siteModuleInr (M N : SiteModule A B) : N ⟶ siteModuleProd A B hA M N :=
  ObjectProperty.homMk (ModuleCat.ofHom (LinearMap.inr A M.obj N.obj))

public theorem siteModuleInl_comp_fst (M N : SiteModule A B) :
    siteModuleInl A B hA M N ≫ siteModuleFst A B hA M N = 𝟙 M := by
  ext
  rfl

public theorem siteModuleInr_comp_snd (M N : SiteModule A B) :
    siteModuleInr A B hA M N ≫ siteModuleSnd A B hA M N = 𝟙 N := by
  ext
  rfl

public theorem siteModuleInr_comp_fst (M N : SiteModule A B) :
    siteModuleInr A B hA M N ≫ siteModuleFst A B hA M N = 0 := by
  ext
  rfl

public theorem siteModuleInl_comp_snd (M N : SiteModule A B) :
    siteModuleInl A B hA M N ≫ siteModuleSnd A B hA M N = 0 := by
  ext
  rfl

include hA in
/-- A natural family of maps between the values of two linear functors on the site modules is
linear at every module: the diagonal product supplies the split square. -/
public theorem isLinearMap_of_natural_siteModule
    (Fu : SiteModule A B ⥤ ModuleCat.{z₁} A)
    (Gu : SiteModule A B ⥤ ModuleCat.{z₂} A)
    [Fu.Additive] [Gu.Additive] [Fu.Linear A] [Gu.Linear A]
    (t : ∀ Z, Fu.obj Z → Gu.obj Z)
    (ht : ∀ {Z W : SiteModule A B} (g : Z ⟶ W) (z : Fu.obj Z),
      t W ((Fu.map g) z) = (Gu.map g) (t Z z))
    (M : SiteModule A B) : IsLinearMap A (t M) :=
  isLinearMap_of_natural_split A Fu Gu t ht M (siteModuleProd A B hA M M)
    (siteModuleFst A B hA M M) (siteModuleSnd A B hA M M)
    (siteModuleInl A B hA M M) (siteModuleInr A B hA M M)
    (siteModuleInl_comp_fst A B hA M M) (siteModuleInr_comp_snd A B hA M M)
    (siteModuleInr_comp_fst A B hA M M) (siteModuleInl_comp_snd A B hA M M)

end SiteModuleSplit

/-! ### A lift class determines its pullback -/

section LiftPullbackUnique
open Functor
universe u v w

variable (A : Type u) [CommRing A] (B : BigFppfSite.{u}) (S : Scheme.{u})
  (hS : B.Contains S) (toS : Spec (.of A) ⟶ S) (hA : B.Contains (Spec (.of A)))
variable {X : Type v} [Category.{w} X] (p : X ⥤ BigFppfOver B S hS) (x : X)
  (hx : p.obj x = algebraOver A B S hS toS hA)

/-- **The pullback of a lift class along a module map is unique.** Two classes of lifts over
`A[N]` both exhibited as the pullback of one class of lifts over `A[M]` agree: the comparison
of their representatives is induced by the universal property of one of the two cartesian
arrows, and is an isomorphism because the lifts of `x` form a category fibred in groupoids.

This is what turns the *relational* naturality field
`Deformation.Artin.TangentFunctorData.liftEquiv_natural` into an equation. -/
public theorem isPullbackOfSquareZeroLift_unique (hp : p.IsFiberedInGroupoids)
    {M N : SiteModule A B} (f : M ⟶ N)
    {a : squareZeroLiftClasses A B S hS toS hA p x hx M}
    {b b' : squareZeroLiftClasses A B S hS toS hA p x hx N}
    (h : IsPullbackOfSquareZeroLift A B S hS toS hA p x hx f a b)
    (h' : IsPullbackOfSquareZeroLift A B S hS toS hA p x hx f a b') : b = b' := by
  obtain ⟨a₁, b₁, ha₁, hb₁, φ₁, hc₁, hw₁⟩ := h
  obtain ⟨a₂, b₂, ha₂, hb₂, φ₂, hc₂, hw₂⟩ := h'
  obtain ⟨ψ⟩ := Quotient.exact (ha₁.trans ha₂.symm)
  have hpsi : p.IsHomLift (𝟙 (squareZeroOver A B S hS toS M)) ψ.hom.1.right :=
    underPost_isHomLift_right p
      (𝟙 (Under.mk (eqToHom hx ≫ squareZeroArrow A B S hS toS hA M) : Under (p.obj x)))
      ψ.hom.1 ψ.hom.2
  have hφ₁ : p.IsHomLift (squareZeroOverMap A B S hS toS f) φ₁ := hc₁.toIsHomLift
  have hcomp : p.IsHomLift (squareZeroOverMap A B S hS toS f) (φ₁ ≫ ψ.hom.1.right) :=
    IsHomLift.comp_lift_id_right' p (squareZeroOverMap A B S hS toS f) φ₁
      (squareZeroOver A B S hS toS M) ψ.hom.1.right
  have hc₂' : p.IsStronglyCartesian (squareZeroOverMap A B S hS toS f) φ₂ := hc₂
  have hsq : squareZeroOverMap A B S hS toS f =
      𝟙 (squareZeroOver A B S hS toS N) ≫ squareZeroOverMap A B S hS toS f := by
    rw [Category.id_comp]
  have hfac : IsStronglyCartesian.map p (squareZeroOverMap A B S hS toS f) φ₂ hsq
      (φ₁ ≫ ψ.hom.1.right) ≫ φ₂ = φ₁ ≫ ψ.hom.1.right :=
    IsStronglyCartesian.fac p (squareZeroOverMap A B S hS toS f) φ₂ hsq (φ₁ ≫ ψ.hom.1.right)
  have hχ : p.IsHomLift (𝟙 (squareZeroOver A B S hS toS N))
      (IsStronglyCartesian.map p (squareZeroOverMap A B S hS toS f) φ₂ hsq
        (φ₁ ≫ ψ.hom.1.right)) :=
    IsStronglyCartesian.map_isHomLift p (squareZeroOverMap A B S hS toS f) φ₂ hsq
      (φ₁ ≫ ψ.hom.1.right)
  have hb₁h : p.IsHomLift (squareZeroArrow A B S hS toS hA N) b₁.1.hom :=
    underFiber_isHomLift p hx (squareZeroArrow A B S hS toS hA N) b₁
  have hb₂h : p.IsHomLift (squareZeroArrow A B S hS toS hA N) b₂.1.hom :=
    underFiber_isHomLift p hx (squareZeroArrow A B S hS toS hA N) b₂
  have hlhs : p.IsHomLift (squareZeroArrow A B S hS toS hA N)
      (b₁.1.hom ≫ IsStronglyCartesian.map p (squareZeroOverMap A B S hS toS f) φ₂ hsq
        (φ₁ ≫ ψ.hom.1.right)) :=
    IsHomLift.comp_lift_id_right' p (squareZeroArrow A B S hS toS hA N) b₁.1.hom
      (squareZeroOver A B S hS toS N) _
  have hw : b₁.1.hom ≫ IsStronglyCartesian.map p (squareZeroOverMap A B S hS toS f) φ₂ hsq
      (φ₁ ≫ ψ.hom.1.right) = b₂.1.hom := by
    refine IsStronglyCartesian.ext p (squareZeroOverMap A B S hS toS f) φ₂
      (squareZeroArrow A B S hS toS hA N) ?_
    rw [Category.assoc, hfac, ← Category.assoc, hw₁, hw₂]
    exact Under.w ψ.hom.1
  rw [← hb₁, ← hb₂]
  have hgpd : IsGroupoid ((Under.post p).Fiber
      (Under.mk (eqToHom hx ≫ squareZeroArrow A B S hS toS hA N) : Under (p.obj x))) :=
    (underPost_isFiberedInGroupoids p hp x).fiber_isGroupoid _
  have θ : b₁ ⟶ b₂ :=
    underFiberHomMk p hx (squareZeroArrow A B S hS toS hA N) (s := b₁) (t := b₂) _ hχ hw
  have hθ : IsIso θ := IsGroupoid.all_isIso θ
  exact Quotient.sound ⟨asIso θ⟩

end LiftPullbackUnique

/-! ### The tangent functor along a 1-morphism -/

section TangentOneMorphism
open Functor
universe u v₁ w₁ v₂ w₂

variable (A : Type u) [CommRing A] (B : BigFppfSite.{u}) (S : Scheme.{u})
  (hS : B.Contains S) (toS : Spec (.of A) ⟶ S) (hA : B.Contains (Spec (.of A)))
variable {X : Type v₁} [Category.{w₁} X] {Y : Type v₂} [Category.{w₂} Y]
  (p : X ⥤ BigFppfOver B S hS) (q : Y ⥤ BigFppfOver B S hS)
  (F : X ⥤ Y) (hF : F ⋙ q = p)
  (x : X) (hx : p.obj x = algebraOver A B S hS toS hA)

include hF hx in
/-- The image of an object over `Spec A` under a `1`-morphism lies over `Spec A`. -/
public theorem oneMorphism_obj_eq : q.obj (F.obj x) = algebraOver A B S hS toS hA :=
  (Functor.congr_obj hF x).trans hx

/-- The functor on lifts of `x` over the trivial square-zero extension `A[M]` induced by a
`1`-morphism. -/
public def squareZeroLiftPost (M : SiteModule A B) :
    (Under.post p).Fiber
        (Under.mk (eqToHom hx ≫ squareZeroArrow A B S hS toS hA M) : Under (p.obj x)) ⥤
      (Under.post q).Fiber
        (Under.mk (eqToHom (oneMorphism_obj_eq A B S hS toS hA p q F hF x hx) ≫
          squareZeroArrow A B S hS toS hA M) : Under (q.obj (F.obj x))) :=
  underFiberPost p q F hF hx (oneMorphism_obj_eq A B S hS toS hA p q F hF x hx)
    (squareZeroArrow A B S hS toS hA M)

/-- **The induced map on lift classes.**  Stacks 07YA for a `1`-morphism: the isomorphism
class of a lift of `x` to `Spec A[M]` is carried to the class of its image, a lift of `F x`
to `Spec A[M]`. -/
public def liftClassOfOneMorphism (M : SiteModule A B) :
    squareZeroLiftClasses A B S hS toS hA p x hx M →
      squareZeroLiftClasses A B S hS toS hA q (F.obj x)
        (oneMorphism_obj_eq A B S hS toS hA p q F hF x hx) M :=
  isoClassMap (squareZeroLiftPost A B S hS toS hA p q F hF x hx M)

public theorem liftClassOfOneMorphism_mk (M : SiteModule A B)
    (t : (Under.post p).Fiber
      (Under.mk (eqToHom hx ≫ squareZeroArrow A B S hS toS hA M) : Under (p.obj x))) :
    liftClassOfOneMorphism A B S hS toS hA p q F hF x hx M (Quotient.mk _ t) =
      Quotient.mk _ ((squareZeroLiftPost A B S hS toS hA p q F hF x hx M).obj t) := rfl

/-- The image of a pullback of lifts is a pullback of lifts: a `1`-morphism of categories
fibred in groupoids preserves strongly cartesian arrows. -/
public theorem isPullbackOfSquareZeroLift_map (hq : q.IsFiberedInGroupoids)
    {M N : SiteModule A B} (f : M ⟶ N)
    (a : squareZeroLiftClasses A B S hS toS hA p x hx M)
    (b : squareZeroLiftClasses A B S hS toS hA p x hx N)
    (h : IsPullbackOfSquareZeroLift A B S hS toS hA p x hx f a b) :
    IsPullbackOfSquareZeroLift A B S hS toS hA q (F.obj x)
      (oneMorphism_obj_eq A B S hS toS hA p q F hF x hx) f
      (liftClassOfOneMorphism A B S hS toS hA p q F hF x hx M a)
      (liftClassOfOneMorphism A B S hS toS hA p q F hF x hx N b) := by
  obtain ⟨a', b', ha', hb', φ, hc, hw⟩ := h
  refine ⟨(squareZeroLiftPost A B S hS toS hA p q F hF x hx M).obj a',
    (squareZeroLiftPost A B S hS toS hA p q F hF x hx N).obj b', ?_, ?_, F.map φ, ?_, ?_⟩
  · rw [← ha']; rfl
  · rw [← hb']; rfl
  · have h0 : p.IsHomLift (squareZeroOverMap A B S hS toS f) φ := hc.toIsHomLift
    have h1 : q.IsHomLift (squareZeroOverMap A B S hS toS f) (F.map φ) :=
      lift_map_isHomLift p q F hF (squareZeroOverMap A B S hS toS f)
        (underFiber_right_obj p hx (squareZeroArrow A B S hS toS hA N) b')
        (underFiber_right_obj p hx (squareZeroArrow A B S hS toS hA M) a') φ h0
    have h2 : q.IsStronglyCartesian (squareZeroOverMap A B S hS toS f) (F.map φ) :=
      hq.isStronglyCartesian_homLift _ _
    exact h2
  · show F.map b'.1.hom ≫ F.map φ = F.map a'.1.hom
    rw [← F.map_comp, hw]

variable (T : TangentFunctorData A B S hS toS hA p x hx)
  (T' : TangentFunctorData A B S hS toS hA q (F.obj x)
    (oneMorphism_obj_eq A B S hS toS hA p q F hF x hx))

/-- **The map `T_x(M) ⟶ T_{F x}(M)` induced by a `1`-morphism.**  Stacks 07YA on the tangent
functor: the map on lift classes read through the two defining bijections.  Nothing is chosen
here — the two tangent functors are *given*, and only their bijections with lift classes are
consumed. -/
public def tangentMapOfOneMorphism (M : SiteModule A B) : T.functor.obj M → T'.functor.obj M :=
  fun z => (T'.liftEquiv M).symm
    (liftClassOfOneMorphism A B S hS toS hA p q F hF x hx M (T.liftEquiv M z))

public theorem liftEquiv_tangentMapOfOneMorphism (M : SiteModule A B) (z : T.functor.obj M) :
    T'.liftEquiv M (tangentMapOfOneMorphism A B S hS toS hA p q F hF x hx T T' M z) =
      liftClassOfOneMorphism A B S hS toS hA p q F hF x hx M (T.liftEquiv M z) :=
  (T'.liftEquiv M).apply_symm_apply _

/-- The induced map is natural in the coordinate module. -/
public theorem tangentMapOfOneMorphism_natural (hq : q.IsFiberedInGroupoids)
    {M N : SiteModule A B} (f : M ⟶ N) (z : T.functor.obj M) :
    tangentMapOfOneMorphism A B S hS toS hA p q F hF x hx T T' N (T.functor.map f z) =
      T'.functor.map f (tangentMapOfOneMorphism A B S hS toS hA p q F hF x hx T T' M z) := by
  apply (T'.liftEquiv N).injective
  rw [liftEquiv_tangentMapOfOneMorphism]
  have h2 := isPullbackOfSquareZeroLift_map A B S hS toS hA p q F hF x hx hq f
    (T.liftEquiv M z) (T.liftEquiv N (T.functor.map f z)) (T.liftEquiv_natural f z)
  have h3 := T'.liftEquiv_natural f
    (tangentMapOfOneMorphism A B S hS toS hA p q F hF x hx T T' M z)
  rw [liftEquiv_tangentMapOfOneMorphism] at h3
  exact isPullbackOfSquareZeroLift_unique A B S hS toS hA q (F.obj x) _ hq f h2 h3

/-- **The induced map on tangent functors is `A`-linear.** -/
public theorem isLinearMap_tangentMapOfOneMorphism (hq : q.IsFiberedInGroupoids)
    (M : SiteModule A B) :
    IsLinearMap A (tangentMapOfOneMorphism A B S hS toS hA p q F hF x hx T T' M) :=
  isLinearMap_of_natural_siteModule A B hA T.functor T'.functor
    (tangentMapOfOneMorphism A B S hS toS hA p q F hF x hx T T')
    (fun g z => tangentMapOfOneMorphism_natural A B S hS toS hA p q F hF x hx T T' hq g z) M

/-- The induced map `T_x(M) ⟶ T_{F x}(M)`, as an `A`-linear map. -/
public def tangentLinearMapOfOneMorphism (hq : q.IsFiberedInGroupoids) (M : SiteModule A B) :
    T.functor.obj M →ₗ[A] T'.functor.obj M :=
  IsLinearMap.mk' (tangentMapOfOneMorphism A B S hS toS hA p q F hF x hx T T' M)
    (isLinearMap_tangentMapOfOneMorphism A B S hS toS hA p q F hF x hx T T' hq M)

@[simp]
public theorem tangentLinearMapOfOneMorphism_apply (hq : q.IsFiberedInGroupoids)
    (M : SiteModule A B) (z : T.functor.obj M) :
    tangentLinearMapOfOneMorphism A B S hS toS hA p q F hF x hx T T' hq M z =
      tangentMapOfOneMorphism A B S hS toS hA p q F hF x hx T T' M z := rfl

end TangentOneMorphism

/-! ### The trivial deformation as a pullback along the retraction -/

section TrivialRetract
open Functor
universe u v w

variable (A : Type u) [CommRing A] (B : BigFppfSite.{u}) (S : Scheme.{u})
  (hS : B.Contains S) (toS : Spec (.of A) ⟶ S) (hA : B.Contains (Spec (.of A)))
variable {X : Type v} [Category.{w} X] (p : X ⥤ BigFppfOver B S hS) (x : X)
  (hx : p.obj x = algebraOver A B S hS toS hA) (hp : p.IsFiberedInGroupoids)

/-- The chosen cartesian arrow exhibiting the trivial deformation of `x` as the pullback of
`x` along the retraction `Spec A[M] ⟶ Spec A`, read in `𝒳` rather than in the lifts. -/
public def trivialRetract (M : SiteModule A B) :
    (trivialDeformation A B S hS toS hA p x hx hp M).1.right ⟶ x :=
  (trivialDeformationMap A B S hS toS hA p x hx hp M).right

public theorem trivialDeformationMap_isCartesian (M : SiteModule A B) :
    (Under.post p).IsCartesian (liftBaseSection A B S hS toS hA p x hx M)
      (trivialDeformationMap A B S hS toS hA p x hx hp M) :=
  have := underPost_isFibered p hp x
  Functor.IsPreFibered.pullbackMap.IsCartesian (liftId A B S hS toS hA p x hx).2
    (liftBaseSection A B S hS toS hA p x hx M)

public theorem trivialRetract_isHomLift (M : SiteModule A B) :
    p.IsHomLift (squareZeroRetraction A B S hS toS hA M)
      (trivialRetract A B S hS toS hA p x hx hp M) :=
  underPost_isHomLift_right p (liftBaseSection A B S hS toS hA p x hx M)
    (trivialDeformationMap A B S hS toS hA p x hx hp M)
    (trivialDeformationMap_isCartesian A B S hS toS hA p x hx hp M).toIsHomLift

/-- The structure arrow of the trivial deformation is a section of the retraction. -/
public theorem trivialRetract_fac (M : SiteModule A B) :
    (trivialDeformation A B S hS toS hA p x hx hp M).1.hom ≫
      trivialRetract A B S hS toS hA p x hx hp M = 𝟙 x :=
  Under.w (trivialDeformationMap A B S hS toS hA p x hx hp M)

/-- The transition arrow of the trivial deformations along a module map, as a morphism of
lifts. -/
public def trivialTransitionUnder {M N : SiteModule A B} (f : M ⟶ N) :
    (trivialDeformation A B S hS toS hA p x hx hp N).1 ⟶
      (trivialDeformation A B S hS toS hA p x hx hp M).1 :=
  letI : (Under.post p : Under x ⥤ Under (p.obj x)).IsFibered := underPost_isFibered p hp x
  Functor.pullbackFiberMap (Under.post p) (liftId A B S hS toS hA p x hx)
    (liftBaseOverMap A B S hS toS hA p x hx f)

public theorem trivialTransitionUnder_isHomLift {M N : SiteModule A B} (f : M ⟶ N) :
    (Under.post p).IsHomLift (liftBaseThickeningMap A B S hS toS hA p x hx f)
      (trivialTransitionUnder A B S hS toS hA p x hx hp f) := by
  have := underPost_isFibered p hp x
  exact Functor.pullbackFiberMap_isHomLift (Under.post p) (liftId A B S hS toS hA p x hx)
    (liftBaseOverMap A B S hS toS hA p x hx f)

/-- The transition arrow of the trivial deformations along a module map, read in `𝒳`. -/
public def trivialTransition {M N : SiteModule A B} (f : M ⟶ N) :
    (trivialDeformation A B S hS toS hA p x hx hp N).1.right ⟶
      (trivialDeformation A B S hS toS hA p x hx hp M).1.right :=
  (trivialTransitionUnder A B S hS toS hA p x hx hp f).right

public theorem trivialTransition_isHomLift {M N : SiteModule A B} (f : M ⟶ N) :
    p.IsHomLift (squareZeroOverMap A B S hS toS f)
      (trivialTransition A B S hS toS hA p x hx hp f) :=
  underPost_isHomLift_right p (liftBaseThickeningMap A B S hS toS hA p x hx f)
    (trivialTransitionUnder A B S hS toS hA p x hx hp f)
    (trivialTransitionUnder_isHomLift A B S hS toS hA p x hx hp f)

/-- The transition arrow is compatible with the two retractions. -/
public theorem trivialTransition_comp_retract {M N : SiteModule A B} (f : M ⟶ N) :
    trivialTransition A B S hS toS hA p x hx hp f ≫
        trivialRetract A B S hS toS hA p x hx hp M =
      trivialRetract A B S hS toS hA p x hx hp N := by
  have := underPost_isFibered p hp x
  have h := Functor.pullbackFiberMap_fac (Under.post p) (liftId A B S hS toS hA p x hx)
    (liftBaseOverMap A B S hS toS hA p x hx f)
  exact congrArg Under.Hom.right h

/-- The transition map of `Inf_x` is restriction along the transition arrow of the trivial
deformations. -/
public theorem infAutSetFunctor_map_eq {M N : SiteModule A B} (f : M ⟶ N)
    (θ : trivialDeformation A B S hS toS hA p x hx hp M ⟶
      trivialDeformation A B S hS toS hA p x hx hp M) :
    (infinitesimalAutomorphismSetFunctor A B S hS toS hA p x hx hp).map f θ =
      fiberEndRestrict (Under.post p) (underPost_isFiberedInGroupoids p hp x)
        (trivialTransitionUnder A B S hS toS hA p x hx hp f)
        (trivialTransitionUnder_isHomLift A B S hS toS hA p x hx hp f) θ := by
  have := underPost_isFibered p hp x
  exact infinitesimalAutomorphismSetFunctor_map A B S hS toS hA p x hx hp f θ

end TrivialRetract

end Deformation.Artin

end
