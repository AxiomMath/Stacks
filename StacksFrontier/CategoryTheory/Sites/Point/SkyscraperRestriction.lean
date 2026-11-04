module

public import Mathlib.CategoryTheory.Sites.Continuous
public import Mathlib.CategoryTheory.Sites.Point.Comap
public import Mathlib.CategoryTheory.Sites.Point.Skyscraper

/-!
# Skyscraper sheaves and restriction along a continuous functor

Let `F : C ⥤ D` be a continuous functor between sites `(C, J)` and `(D, K)`, let `p` be a point
of `(C, J)` and `q` a point of `(D, K)`, and suppose the fibre functor of `q` pulled back along
`F` is isomorphic to the fibre functor of `p`. Then restriction of sheaves along `F` carries the
skyscraper sheaf of `q` at an object to the skyscraper sheaf of `p` at that object, naturally.

Mathlib's
`CategoryTheory.GrothendieckTopology.Point.skyscraperSheafFunctorCompSheafPushforwardContinuous`
is the case where the point of `(C, J)` is `q.comap F`, whose fibre functor is `F ⋙ q.fiber` on
the nose; the statement here asks only for an isomorphism of fibre functors, which is what a
point described independently of `F` — a geometric point of an algebraic space, say — provides.
It also needs neither representable flatness of `F` nor an initial smallness hypothesis, because
no new point is constructed.

## Main results

* `CategoryTheory.GrothendieckTopology.Point`'s
  `skyscraperSheafFunctorCompSheafPushforwardContinuousIso`: the isomorphism of skyscraper sheaf
  functors.

## Implementation notes

A skyscraper presheaf is a pointwise product of copies of the object indexed by the fibre, so
the skyscraper presheaf functor is the flip of `CategoryTheory.Limits.piFunctor` precomposed with
the opposite of the fibre functor. Restriction of presheaves along `F` precomposes the fibre
functor with `F`, so the isomorphism of fibre functors transports to an isomorphism of
skyscraper presheaf functors by functoriality of flipping. Since `sheafToPresheaf` is fully
faithful, postcomposition with it is fully faithful too, and the isomorphism of sheaf functors is
the preimage of that one.
-/

@[expose] public noncomputable section

namespace CategoryTheory.GrothendieckTopology.Point

open Limits

universe w v

variable {C D : Type*} [Category* C] [Category* D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}

/-- Restriction of sheaves along a continuous functor `F : (C, J) ⥤ (D, K)` carries the
skyscraper sheaf functor of a point `q` of `(D, K)` to the skyscraper sheaf functor of a point
`p` of `(C, J)`, given an isomorphism `F ⋙ q.fiber ≅ p.fiber` of fibre functors. -/
def skyscraperSheafFunctorCompSheafPushforwardContinuousIso (p : Point.{w} J) (q : Point.{w} K)
    (F : C ⥤ D) [F.IsContinuous J K] (e : F ⋙ q.fiber ≅ p.fiber)
    (A : Type*) [Category.{v} A] [HasProducts.{w} A] :
    q.skyscraperSheafFunctor (A := A) ⋙ F.sheafPushforwardContinuous A J K ≅
      p.skyscraperSheafFunctor :=
  ((fullyFaithfulSheafToPresheaf J A).whiskeringRight A).preimageIso
    ((flipFunctor _ _ A).mapIso (Functor.isoWhiskerRight (NatIso.op e.symm) piFunctor.flip))

end CategoryTheory.GrothendieckTopology.Point

end
