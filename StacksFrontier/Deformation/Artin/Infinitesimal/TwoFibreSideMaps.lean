module

public import StacksFrontier.Deformation.Artin.Infinitesimal.Functoriality

/-!
# The comparison maps of the `𝒵`-side of the six-term sequence

Let `p : 𝒳 ⟶ 𝒴` and `q : 𝒵 ⟶ 𝒴` be `1`-morphisms of categories fibred in groupoids over the
big fppf site of a scheme `S`, let `A` be an `S`-algebra and let `w` be an object of the
`2`-fibre product `𝒲 = 𝒳 ×_𝒴 𝒵` over `Spec A`, with components `x`, `z` and comparison
isomorphism `w.iso : p x ≅ q z`.  The six-term sequence of Stacks 0DNN has `Inf_y(M)` and
`T_y(M)` for `y = p x` in its third and sixth places, so the maps out of the `𝒵`-side are
*not* the maps induced by `q` alone: they are those followed by the identification of the
invariants of `q z` with those of `p x` along `w.iso`.

This file builds that composite in the generality in which it holds: for a `1`-morphism
`F : X ⟶ Y` over the site, an object `x` of `X` over `Spec A`, an object `y` of `Y` over
`Spec A` and a *vertical* isomorphism `ι : y ≅ F x`, there are `A`-linear maps

`T_x(M) ⟶ T_y(M)` and `Inf_x(M) ⟶ Inf_y(M)`,

namely the maps of Stacks 07YA induced by `F` followed by the transport along `ι`.  Taking
`F = q`, `x = z`, `y = p x` and `ι = w.iso` gives exactly the two `𝒵`-side maps of the
six-term sequence.

## Main definitions

* `Deformation.Artin.liftClassOfOneMorphismTransport`: the induced map on isomorphism classes
  of lifts over the trivial square-zero extension `A[M]`.
* `Deformation.Artin.tangentMapOfOneMorphismTransport`,
  `Deformation.Artin.tangentLinearMapOfOneMorphismTransport`: the map `T_x(M) ⟶ T_y(M)`, read
  through the two `liftEquiv` bijections, and the same map packaged as an `A`-linear map.
* `Deformation.Artin.infMapOfOneMorphismTransport`: the map on automorphisms of the trivial
  deformations.
* `Deformation.Artin.infFunctorMapOfOneMorphismTransport`,
  `Deformation.Artin.infLinearMapOfOneMorphismTransport`: the map `Inf_x(M) ⟶ Inf_y(M)`, read
  through the two `autEquiv` bijections, and the same map packaged as an `A`-linear map.

## Main results

* `Deformation.Artin.isPullbackOfSquareZeroLift_mapTransport`: the composite carries a
  pullback of lifts to a pullback of lifts.
* `Deformation.Artin.tangentMapOfOneMorphismTransport_natural`,
  `Deformation.Artin.isLinearMap_tangentMapOfOneMorphismTransport`: the tangent-side map is
  natural in `M` and `A`-linear.
* `Deformation.Artin.infMapOfOneMorphismTransport_natural`,
  `Deformation.Artin.infFunctorMapOfOneMorphismTransport_natural`,
  `Deformation.Artin.isLinearMap_infFunctorMapOfOneMorphismTransport`: the same for the
  `Inf`-side map.

## References

* [Stacks Project, Tag 07YA](https://stacks.math.columbia.edu/tag/07YA)
* [Stacks Project, Tag 0DNN](https://stacks.math.columbia.edu/tag/0DNN)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace Deformation.Artin

/-! ### A 1-morphism followed by a vertical isomorphism -/

section OneMorphismTransport
open Functor
universe u v₁ w₁ v₂ w₂

variable (A : Type u) [CommRing A] (B : BigFppfSite.{u}) (S : Scheme.{u})
  (hS : B.Contains S) (toS : Spec (.of A) ⟶ S) (hA : B.Contains (Spec (.of A)))
variable {X : Type v₁} [Category.{w₁} X] {Y : Type v₂} [Category.{w₂} Y]
  (p : X ⥤ BigFppfOver B S hS) (q : Y ⥤ BigFppfOver B S hS)
  (F : X ⥤ Y) (hF : F ⋙ q = p)
  (x : X) (hx : p.obj x = algebraOver A B S hS toS hA)
  (y : Y) (hy : q.obj y = algebraOver A B S hS toS hA)
  (ι : y ≅ F.obj x) (hι : q.IsHomLift (𝟙 (algebraOver A B S hS toS hA)) ι.hom)
  (hp : p.IsFiberedInGroupoids) (hq : q.IsFiberedInGroupoids)

/-- **The map on lift classes induced by a `1`-morphism followed by a vertical
isomorphism**: the class of a lift of `x` over `Spec A[M]` is carried to the class of its
image under `F`, read as a lift of `y` through `ι`. -/
public def liftClassOfOneMorphismTransport (M : SiteModule A B) :
    squareZeroLiftClasses A B S hS toS hA p x hx M →
      squareZeroLiftClasses A B S hS toS hA q y hy M :=
  fun a => liftClassOfTransport A B S hS toS hA q y (F.obj x) hy
    (oneMorphism_obj_eq A B S hS toS hA p q F hF x hx) ι hι M
    (liftClassOfOneMorphism A B S hS toS hA p q F hF x hx M a)

include hq in
/-- The composite carries a pullback of lifts to a pullback of lifts. -/
public theorem isPullbackOfSquareZeroLift_mapTransport
    {M N : SiteModule A B} (f : M ⟶ N)
    (a : squareZeroLiftClasses A B S hS toS hA p x hx M)
    (b : squareZeroLiftClasses A B S hS toS hA p x hx N)
    (h : IsPullbackOfSquareZeroLift A B S hS toS hA p x hx f a b) :
    IsPullbackOfSquareZeroLift A B S hS toS hA q y hy f
      (liftClassOfOneMorphismTransport A B S hS toS hA p q F hF x hx y hy ι hι M a)
      (liftClassOfOneMorphismTransport A B S hS toS hA p q F hF x hx y hy ι hι N b) :=
  isPullbackOfSquareZeroLift_transport A B S hS toS hA q y (F.obj x) hy
    (oneMorphism_obj_eq A B S hS toS hA p q F hF x hx) ι hι f _ _
    (isPullbackOfSquareZeroLift_map A B S hS toS hA p q F hF x hx hq f a b h)

variable (T : TangentFunctorData A B S hS toS hA p x hx)
  (T' : TangentFunctorData A B S hS toS hA q y hy)

/-- **The map `T_x(M) ⟶ T_y(M)` induced by a `1`-morphism followed by a vertical
isomorphism**, read through the two defining bijections. -/
public def tangentMapOfOneMorphismTransport (M : SiteModule A B) :
    T.functor.obj M → T'.functor.obj M :=
  fun z => (T'.liftEquiv M).symm
    (liftClassOfOneMorphismTransport A B S hS toS hA p q F hF x hx y hy ι hι M
      (T.liftEquiv M z))

/-- The tangent-side map read back through the bijection of `T'` is the map on lift
classes. -/
public theorem liftEquiv_tangentMapOfOneMorphismTransport (M : SiteModule A B)
    (z : T.functor.obj M) :
    T'.liftEquiv M
        (tangentMapOfOneMorphismTransport A B S hS toS hA p q F hF x hx y hy ι hι T T' M z) =
      liftClassOfOneMorphismTransport A B S hS toS hA p q F hF x hx y hy ι hι M
        (T.liftEquiv M z) :=
  (T'.liftEquiv M).apply_symm_apply _

include hq in
/-- The induced map is natural in the coordinate module. -/
public theorem tangentMapOfOneMorphismTransport_natural
    {M N : SiteModule A B} (f : M ⟶ N) (z : T.functor.obj M) :
    tangentMapOfOneMorphismTransport A B S hS toS hA p q F hF x hx y hy ι hι T T' N
        (T.functor.map f z) =
      T'.functor.map f
        (tangentMapOfOneMorphismTransport A B S hS toS hA p q F hF x hx y hy ι hι T T' M z) := by
  apply (T'.liftEquiv N).injective
  rw [liftEquiv_tangentMapOfOneMorphismTransport]
  have h2 := isPullbackOfSquareZeroLift_mapTransport A B S hS toS hA p q F hF x hx y hy ι hι
    hq f (T.liftEquiv M z) (T.liftEquiv N (T.functor.map f z)) (T.liftEquiv_natural f z)
  have h3 := T'.liftEquiv_natural f
    (tangentMapOfOneMorphismTransport A B S hS toS hA p q F hF x hx y hy ι hι T T' M z)
  rw [liftEquiv_tangentMapOfOneMorphismTransport] at h3
  exact isPullbackOfSquareZeroLift_unique A B S hS toS hA q y hy hq f h2 h3

include hq in
/-- **The induced map on tangent functors is `A`-linear.** -/
public theorem isLinearMap_tangentMapOfOneMorphismTransport (M : SiteModule A B) :
    IsLinearMap A
      (tangentMapOfOneMorphismTransport A B S hS toS hA p q F hF x hx y hy ι hι T T' M) :=
  isLinearMap_of_natural_siteModule A B hA T.functor T'.functor
    (tangentMapOfOneMorphismTransport A B S hS toS hA p q F hF x hx y hy ι hι T T')
    (fun g u => tangentMapOfOneMorphismTransport_natural A B S hS toS hA p q F hF x hx y hy
      ι hι hq T T' g u) M

/-- The induced map `T_x(M) ⟶ T_y(M)`, as an `A`-linear map. -/
public def tangentLinearMapOfOneMorphismTransport (M : SiteModule A B) :
    T.functor.obj M →ₗ[A] T'.functor.obj M :=
  IsLinearMap.mk'
    (tangentMapOfOneMorphismTransport A B S hS toS hA p q F hF x hx y hy ι hι T T' M)
    (isLinearMap_tangentMapOfOneMorphismTransport A B S hS toS hA p q F hF x hx y hy ι hι hq
      T T' M)

/-- The `A`-linear map `T_x(M) ⟶ T_y(M)` agrees with the underlying induced map. -/
@[simp]
public theorem tangentLinearMapOfOneMorphismTransport_apply (M : SiteModule A B)
    (z : T.functor.obj M) :
    tangentLinearMapOfOneMorphismTransport A B S hS toS hA p q F hF x hx y hy ι hι hq
        T T' M z =
      tangentMapOfOneMorphismTransport A B S hS toS hA p q F hF x hx y hy ι hι T T' M z := rfl

/-- **The map on infinitesimal automorphisms induced by a `1`-morphism followed by a vertical
isomorphism**: the image under `F` of an automorphism of the trivial deformation of `x`,
restricted to the trivial deformation of `F x` and then transported along `ι`. -/
public def infMapOfOneMorphismTransport (M : SiteModule A B)
    (θ : trivialDeformation A B S hS toS hA p x hx hp M ⟶
      trivialDeformation A B S hS toS hA p x hx hp M) :
    trivialDeformation A B S hS toS hA q y hy hq M ⟶
      trivialDeformation A B S hS toS hA q y hy hq M :=
  infMapOfTransport A B S hS toS hA q y (F.obj x) hy
    (oneMorphism_obj_eq A B S hS toS hA p q F hF x hx) ι hι hq M
    (infMapOfOneMorphism A B S hS toS hA p q F hF x hx hp hq M θ)

/-- The induced map on automorphisms of the trivial deformations is natural in the module. -/
public theorem infMapOfOneMorphismTransport_natural {M N : SiteModule A B} (f : M ⟶ N)
    (θ : trivialDeformation A B S hS toS hA p x hx hp M ⟶
      trivialDeformation A B S hS toS hA p x hx hp M) :
    infMapOfOneMorphismTransport A B S hS toS hA p q F hF x hx y hy ι hι hp hq N
        ((infinitesimalAutomorphismSetFunctor A B S hS toS hA p x hx hp).map f θ) =
      (infinitesimalAutomorphismSetFunctor A B S hS toS hA q y hy hq).map f
        (infMapOfOneMorphismTransport A B S hS toS hA p q F hF x hx y hy ι hι hp hq M θ) :=
  (congrArg (infMapOfTransport A B S hS toS hA q y (F.obj x) hy
      (oneMorphism_obj_eq A B S hS toS hA p q F hF x hx) ι hι hq N)
    (infMapOfOneMorphism_natural A B S hS toS hA p q F hF x hx hp hq f θ)).trans
    (infMapOfTransport_natural A B S hS toS hA q y (F.obj x) hy
      (oneMorphism_obj_eq A B S hS toS hA p q F hF x hx) ι hι hq f
      (infMapOfOneMorphism A B S hS toS hA p q F hF x hx hp hq M θ))

variable (Inf : InfinitesimalAutomorphismFunctorData A B S hS toS hA p x hx hp)
  (Inf' : InfinitesimalAutomorphismFunctorData A B S hS toS hA q y hy hq)

/-- **The map `Inf_x(M) ⟶ Inf_y(M)` induced by a `1`-morphism followed by a vertical
isomorphism**, read through the two defining bijections. -/
public def infFunctorMapOfOneMorphismTransport (M : SiteModule A B) :
    Inf.functor.obj M → Inf'.functor.obj M :=
  fun u => (Inf'.autEquiv M).symm
    (infMapOfOneMorphismTransport A B S hS toS hA p q F hF x hx y hy ι hι hp hq M
      (Inf.autEquiv M u))

/-- The `Inf`-side map read back through the bijection of `Inf'` is the map on automorphisms
of the trivial deformations. -/
public theorem autEquiv_infFunctorMapOfOneMorphismTransport (M : SiteModule A B)
    (u : Inf.functor.obj M) :
    Inf'.autEquiv M
        (infFunctorMapOfOneMorphismTransport A B S hS toS hA p q F hF x hx y hy ι hι hp hq
          Inf Inf' M u) =
      infMapOfOneMorphismTransport A B S hS toS hA p q F hF x hx y hy ι hι hp hq M
        (Inf.autEquiv M u) :=
  (Inf'.autEquiv M).apply_symm_apply _

/-- The induced map on the functors of infinitesimal automorphisms is natural in the
module. -/
public theorem infFunctorMapOfOneMorphismTransport_natural {M N : SiteModule A B} (f : M ⟶ N)
    (u : Inf.functor.obj M) :
    infFunctorMapOfOneMorphismTransport A B S hS toS hA p q F hF x hx y hy ι hι hp hq
        Inf Inf' N (Inf.functor.map f u) =
      Inf'.functor.map f
        (infFunctorMapOfOneMorphismTransport A B S hS toS hA p q F hF x hx y hy ι hι hp hq
          Inf Inf' M u) := by
  apply (Inf'.autEquiv N).injective
  rw [autEquiv_infFunctorMapOfOneMorphismTransport, Inf.autEquiv_natural,
    Inf'.autEquiv_natural, autEquiv_infFunctorMapOfOneMorphismTransport]
  exact infMapOfOneMorphismTransport_natural A B S hS toS hA p q F hF x hx y hy ι hι hp hq
    f (Inf.autEquiv M u)

/-- **The induced map on infinitesimal automorphisms is `A`-linear.** -/
public theorem isLinearMap_infFunctorMapOfOneMorphismTransport (M : SiteModule A B) :
    IsLinearMap A
      (infFunctorMapOfOneMorphismTransport A B S hS toS hA p q F hF x hx y hy ι hι hp hq
        Inf Inf' M) :=
  isLinearMap_of_natural_siteModule A B hA Inf.functor Inf'.functor
    (infFunctorMapOfOneMorphismTransport A B S hS toS hA p q F hF x hx y hy ι hι hp hq
      Inf Inf')
    (fun g u => infFunctorMapOfOneMorphismTransport_natural A B S hS toS hA p q F hF x hx
      y hy ι hι hp hq Inf Inf' g u) M

/-- The induced map `Inf_x(M) ⟶ Inf_y(M)`, as an `A`-linear map. -/
public def infLinearMapOfOneMorphismTransport (M : SiteModule A B) :
    Inf.functor.obj M →ₗ[A] Inf'.functor.obj M :=
  IsLinearMap.mk'
    (infFunctorMapOfOneMorphismTransport A B S hS toS hA p q F hF x hx y hy ι hι hp hq
      Inf Inf' M)
    (isLinearMap_infFunctorMapOfOneMorphismTransport A B S hS toS hA p q F hF x hx y hy ι hι
      hp hq Inf Inf' M)

/-- The `A`-linear map `Inf_x(M) ⟶ Inf_y(M)` agrees with the underlying induced map. -/
@[simp]
public theorem infLinearMapOfOneMorphismTransport_apply (M : SiteModule A B)
    (u : Inf.functor.obj M) :
    infLinearMapOfOneMorphismTransport A B S hS toS hA p q F hF x hx y hy ι hι hp hq
        Inf Inf' M u =
      infFunctorMapOfOneMorphismTransport A B S hS toS hA p q F hF x hx y hy ι hι hp hq
        Inf Inf' M u := rfl

end OneMorphismTransport

end Deformation.Artin

end
