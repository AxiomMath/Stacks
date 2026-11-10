module

public import Mathlib.CategoryTheory.Functor.ReflectsIso.Jointly
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FinitePushforwardBaseChange
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GeometricPointDomination
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.PullbackStalk.Basic
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.EnoughGeometricPoints
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Inverse images along a jointly surjective family of morphisms are jointly faithful

Let `B` be a big étale site, `X` an object of `B` and `Y i ⟶ X`, `i : Fin k`, a finite family of
morphisms which is jointly surjective on underlying spaces. The family of inverse-image functors
on sheaves of sets on the small étale sites is then *jointly faithful*: two morphisms of sheaves
of sets on `X_étale` whose inverse images along all the `Y i ⟶ X` agree are equal.

The argument is the stalk argument of Stacks 03PU. Two morphisms of sheaves of sets with the same
germ at every geometric point of `X` are equal, because over each object of the small étale site
the sieve on which the two images of a section become equal admits, above every point, a member
through which that point lifts, hence is covering, and a sheaf is separated for a covering sieve.
The hypothesis gives equality of germs only at the geometric points factoring through one of the
`Y i`: the stalk of an inverse image at a geometric point of `Y i` is the stalk at its image
(Stacks 03Q1). Joint surjectivity makes the *image points* of those geometric points exhaust `X`,
and the étale stalk functor at a geometric point depends only on the point of `X` beneath it
(Stacks 04FN), which upgrades equality of germs at that subfamily to equality at every geometric
point.

## Main results

* `AlgebraicGeometry.eq_of_etaleStalkPresheafFunctor_map_eq` — two morphisms of sheaves of sets
  on the small étale site inducing the same map on every stalk at a geometric point are equal.
* `AlgebraicGeometry.jointlyFaithful_etaleStalkFunctor` — the étale stalk functors at the
  geometric points are jointly faithful on sheaves of sets.
* `AlgebraicGeometry.jointlyFaithful_smallEtaleSetPullback` — **the inverse-image functors along
  a finite jointly surjective family are jointly faithful** on sheaves of sets.

## References

* [Stacks Project, Tag 03PU](https://stacks.math.columbia.edu/tag/03PU)
* [Stacks Project, Tag 03Q1](https://stacks.math.columbia.edu/tag/03Q1)
* [Stacks Project, Tag 04FN](https://stacks.math.columbia.edu/tag/04FN)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry

section Stalks

variable (B : BigEtaleSite.{u}) (X : Scheme.{u}) (hX : B.Contains X)

/-- **Two morphisms of sheaves of sets on the small étale site with the same germs are equal.**
Over every object of the site the sieve on which the two images of a section agree is covering,
because the germ of a section at the geometric point attached to a point of that object is
computed on étale neighbourhoods; a sheaf is separated for a covering sieve. -/
@[sga "4 VIII 3.7" "partial"]
public theorem eq_of_etaleStalkPresheafFunctor_map_eq
    {F G : Sheaf (SmallEtale.topology B X hX) (Type (u + 1))} (α β : F ⟶ G)
    (h : ∀ s : GeometricPoint X,
      (etaleStalkPresheafFunctor B X hX s (Type (u + 1))).map α.hom =
        (etaleStalkPresheafFunctor B X hX s (Type (u + 1))).map β.hom) :
    α = β := by
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext V
  ext a
  obtain ⟨V⟩ := V
  have hcov : Presheaf.equalizerSieve (F := G.obj) (X := op V)
      (α.hom.app (op V) a) (β.hom.app (op V) a) ∈ SmallEtale.topology B X hX V := by
    apply SmallEtale.mem_topology_of_jointlySurjective
    intro x
    let s := geometricPointOfEtalePoint B X hX V x
    let Φ := geometricPointSitePoint B X hX s
    let p : Φ.fiber.obj V := geometricPointOfEtalePointLift B X hX V x
    have hgerm : Φ.toPresheafFiber V p G.obj (α.hom.app (op V) a) =
        Φ.toPresheafFiber V p G.obj (β.hom.app (op V) a) := by
      have key := ConcreteCategory.congr_hom (h s) (Φ.toPresheafFiber V p F.obj a)
      change Φ.presheafFiber.map α.hom (Φ.toPresheafFiber V p F.obj a) =
        Φ.presheafFiber.map β.hom (Φ.toPresheafFiber V p F.obj a) at key
      rwa [Φ.toPresheafFiber_naturality_apply α.hom,
        Φ.toPresheafFiber_naturality_apply β.hom] at key
    obtain ⟨W, k, y', hy', heq⟩ :=
      (Φ.toPresheafFiber_eq_iff' (P := G.obj) V p (α.hom.app (op V) a)
        (β.hom.app (op V) a)).1 hgerm
    refine ⟨W, k, heq, ⟨y'.1 default, ?_⟩⟩
    have h1 : y'.1 ≫ (SmallEtale.toScheme B X hX).map k = p.1 := congrArg Subtype.val hy'
    rw [← geometricPointOfEtalePointLift_base B X hX V x, ← h1]
    rfl
  exact G.property.isSeparated _ _ hcov _ _ fun _ _ hf => hf

/-- **The étale stalk functors at the geometric points are jointly faithful on sheaves of
sets.** This is the faithfulness contained in Stacks 03PU for set coefficients. -/
public theorem jointlyFaithful_etaleStalkFunctor :
    JointlyFaithful (fun s : GeometricPoint X => etaleStalkFunctor.{u, u + 1} B X hX s) :=
  ⟨fun {_ _} {α β} h => eq_of_etaleStalkPresheafFunctor_map_eq B X hX α β h⟩

end Stalks

/-- Equal images of two morphisms under `P` give equal images under `Q`, for `e : P ≅ Q`. -/
private theorem map_eq_map_of_iso_hom {C D : Type*} [Category C] [Category D] {P Q : C ⥤ D}
    (e : P ≅ Q) {A A' : C} (f g : A ⟶ A') (h : P.map f = P.map g) : Q.map f = Q.map g := by
  refine (cancel_epi (e.hom.app A)).1 ?_
  rw [← e.hom.naturality f, ← e.hom.naturality g, h]

/-- **Inverse image along a finite jointly surjective family is jointly faithful** on sheaves of
sets on the small étale sites: two morphisms of sheaves of sets on `X_étale` whose inverse images
along every member of the family agree are equal.

The stalk of the inverse image along `Y i ⟶ X` at a geometric point of `Y i` is the stalk at the
image geometric point, so the hypothesis gives equality of the maps on the stalks at the
geometric points of `X` factoring through some `Y i`. Joint surjectivity provides, above every
point of `X`, a point of some `Y i`, hence a geometric point of that form with the same image
point; the étale stalk functor depends only on that image point, so the maps agree on all
stalks. -/
@[sga "4 VIII 9.1" "special case"]
public theorem jointlyFaithful_smallEtaleSetPullback
    (B : BigEtaleSite.{u}) (X : B.Scheme) {k : ℕ} (Y : Fin k → B.Scheme)
    (inclusions : ∀ i, Y i ⟶ X)
    (hsurj : ∀ x : X.obj, ∃ (i : Fin k) (y : (Y i).obj),
      (B.inclusion.map (inclusions i)) y = x) :
    JointlyFaithful (fun i => (smallEtaleBaseChange B (inclusions i)).sheafPullback
      (Type (u + 1)) (SmallEtale.topology B X.obj X.property)
      (SmallEtale.topology B (Y i).obj (Y i).property)) := by
  refine ⟨fun {F G} {α β} h => ?_⟩
  refine eq_of_etaleStalkPresheafFunctor_map_eq B X.obj X.property α β fun s => ?_
  obtain ⟨i, y, hy⟩ := hsurj (s.hom default)
  set x : GeometricPoint (Y i).obj := GeometricPoint.ofPoint (Y i).obj y with hxdef
  have hbase : (x.map (B.inclusion.map (inclusions i))).hom default = s.hom default := by
    change (B.inclusion.map (inclusions i)).base (x.hom default) = s.hom default
    rwa [hxdef, GeometricPoint.ofPoint_liesOver]
  -- The stalk of the inverse image at `x` is the stalk at the image point of `x`.
  have hpushed := map_eq_map_of_iso_hom (smallEtalePullbackStalkIso B (inclusions i) x) α β
    (congrArg (etaleStalkFunctor.{u, u + 1} B (Y i).obj (Y i).property x).map (h i))
  exact map_eq_map_of_iso_hom
    (etaleStalkPresheafFunctorIsoOfEqBase B X.obj X.property hbase (Type (u + 1)))
    α.hom β.hom hpushed

end AlgebraicGeometry

end
