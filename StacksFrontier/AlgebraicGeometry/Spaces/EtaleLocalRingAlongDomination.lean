module

public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.FlatEtaleLocalRing
public import StacksFrontier.AlgebraicGeometry.Spaces.StalkIndependenceOfGeometricPoint

/-!
# Étale local rings along a domination of geometric points

Stacks 04K4 says that the stalk functors on the small étale site at two geometric points of an
algebraic space lying over the same point of the space are isomorphic, and
`AlgebraicGeometry.Space.stalkFunctorIsoAlong` produces the isomorphism along an explicit
domination.  Taken at the structure presheaf that isomorphism is a ring isomorphism of étale
local rings, and this file proves its compatibility with
`AlgebraicGeometry.Space.etaleLocalRingGerm` and with the canonical homomorphism
`AlgebraicGeometry.Space.etaleLocalRingMap` of Stacks 04NG.

Consequently a regular sequence of germs of sections in the étale local ring at a geometric
point remains one at any geometric point dominating it, over an enlarged field.

## Main definitions

* `AlgebraicGeometry.Space.etaleLocalRingIsoAlong`: the isomorphism `𝒪_{F, x̄} ≅ 𝒪_{F, ȳ}` of
  étale local rings along a domination `ȳ → x̄` of geometric points, namely
  `AlgebraicGeometry.Space.stalkFunctorIsoAlong` taken at the structure presheaf.
* `AlgebraicGeometry.Space.etaleLocalRingIsoAlongMap`: the same isomorphism for the images of
  the two geometric points under a morphism `p : F ⟶ G`.

## Main results

* `AlgebraicGeometry.Space.etaleLocalRingIsoAlong_germ`: the comparison isomorphism carries the
  germ at `x̄` of a section on a small étale neighbourhood to its germ at `ȳ` on the restricted
  neighbourhood.
* `AlgebraicGeometry.Space.etaleLocalRingIsoAlong_germ_of_lift` and
  `AlgebraicGeometry.Space.etaleLocalRingIsoAlong_inv_germ_of_lift`: the same statement, and its
  inverse, phrased for a neighbourhood of `ȳ` together with a lift of `x̄` to its chart.
* `AlgebraicGeometry.Space.isEtaleLocalRingMap_etaleLocalRingIsoAlong` and
  `AlgebraicGeometry.Space.etaleLocalRingIsoAlong_comp_etaleLocalRingMap`: the canonical
  homomorphisms of étale local rings of Stacks 04NG commute with the comparison isomorphisms,
  i.e. the square relating `𝒪_{G, p∘x̄} ⟶ 𝒪_{F, x̄}` to `𝒪_{G, p∘ȳ} ⟶ 𝒪_{F, ȳ}` commutes.
* `AlgebraicGeometry.Space.isRegular_ofFn_etaleLocalRingMap_germ_along`: a regular sequence of
  germs transported along a domination of geometric points.

## References

* [Stacks Project, Tag 04K4](https://stacks.math.columbia.edu/tag/04K4)
* [Stacks Project, Tag 04KG](https://stacks.math.columbia.edu/tag/04KG)
* [Stacks Project, Tag 04NG](https://stacks.math.columbia.edu/tag/04NG)
* [Stacks Project, Lemma 06LW](https://stacks.math.columbia.edu/tag/06LW)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- The isomorphism of étale local rings along a domination of geometric points. -/
noncomputable def etaleLocalRingIsoAlong (hF : IsAlgebraicSpace B S hS F)
    {x y : GeometricPoint B S hS F}
    (f : y.val.siteObject ⟶ x.val.siteObject)
    (hf : F.map f.op x.val.value = y.val.value) :
    etaleLocalRing B S hS F x ≅ etaleLocalRing B S hS F y :=
  (stalkFunctorIsoAlong hF CommRingCat.{u + 1} f hf).app (liftedStructurePresheaf B S hS F)

/-- The comparison isomorphism along a domination carries the germ at `x` of a section on a small
étale neighbourhood `U` to its germ at `y` on the restricted neighbourhood
`(neighborhoodAlong f hf).obj U`. -/
theorem etaleLocalRingIsoAlong_germ (hF : IsAlgebraicSpace B S hS F)
    {x y : GeometricPoint B S hS F}
    (f : y.val.siteObject ⟶ x.val.siteObject)
    (hf : F.map f.op x.val.value = y.val.value)
    (U : SmallEtaleNeighborhood x)
    (a : (structurePresheaf B S hS F).obj (Opposite.op U.chart)) :
    (etaleLocalRingIsoAlong hF f hf).hom.hom
        (etaleLocalRingGerm B S hS F x (Opposite.op U) a) =
      etaleLocalRingGerm B S hS F y
        (Opposite.op ((neighborhoodAlong f hf).obj U)) a := by
  classical
  let : Functor.Initial (neighborhoodAlong (B := B) (S := S) (hS := hS) (F := F) f hf) :=
    neighborhoodAlong_initial hF f hf
  let : Functor.Final (neighborhoodAlong (B := B) (S := S) (hS := hS) (F := F) f hf).op :=
    Functor.final_op_of_initial _
  exact congrArg (fun q => CommRingCat.Hom.hom q (ULift.up a)) <| Functor.Final.ι_colimitIso_hom
    (neighborhoodAlong (B := B) (S := S) (hS := hS) (F := F) f hf).op
    (SmallEtaleNeighborhood.sections (x := y) (liftedStructurePresheaf B S hS F))
    (Opposite.op U)

/-- The comparison isomorphism along a domination carries the germ at the dominated point of a
section on a chart to its germ at the dominating point, for any lift of the dominated point to
the chart of a neighbourhood of the dominating one. -/
theorem etaleLocalRingIsoAlong_germ_of_lift (hF : IsAlgebraicSpace B S hS F)
    {x y : GeometricPoint B S hS F}
    (f : y.val.siteObject ⟶ x.val.siteObject)
    (hf : F.map f.op x.val.value = y.val.value)
    (c : SmallEtale B S hS F) (z : x.val.siteObject ⟶ c.obj.left)
    (hz : c.obj.hom.app (Opposite.op x.val.siteObject) z = x.val.value)
    (pt : y.val.siteObject ⟶ c.obj.left)
    (hpt : c.obj.hom.app (Opposite.op y.val.siteObject) pt = y.val.value)
    (hfz : f ≫ z = pt)
    (a : (structurePresheaf B S hS F).obj (Opposite.op c)) :
    (etaleLocalRingIsoAlong hF f hf).hom.hom
        (etaleLocalRingGerm B S hS F x (Opposite.op ⟨c, z, hz⟩) a) =
      etaleLocalRingGerm B S hS F y (Opposite.op ⟨c, pt, hpt⟩) a := by
  subst hfz
  exact etaleLocalRingIsoAlong_germ hF f hf ⟨c, z, hz⟩ a

/-- The inverse of the comparison isomorphism along a domination carries a germ at the
dominating point back to the germ at the dominated one. -/
theorem etaleLocalRingIsoAlong_inv_germ_of_lift (hF : IsAlgebraicSpace B S hS F)
    {x y : GeometricPoint B S hS F}
    (f : y.val.siteObject ⟶ x.val.siteObject)
    (hf : F.map f.op x.val.value = y.val.value)
    (c : SmallEtale B S hS F) (z : x.val.siteObject ⟶ c.obj.left)
    (hz : c.obj.hom.app (Opposite.op x.val.siteObject) z = x.val.value)
    (pt : y.val.siteObject ⟶ c.obj.left)
    (hpt : c.obj.hom.app (Opposite.op y.val.siteObject) pt = y.val.value)
    (hfz : f ≫ z = pt)
    (a : (structurePresheaf B S hS F).obj (Opposite.op c)) :
    (etaleLocalRingIsoAlong hF f hf).inv.hom
        (etaleLocalRingGerm B S hS F y (Opposite.op ⟨c, pt, hpt⟩) a) =
      etaleLocalRingGerm B S hS F x (Opposite.op ⟨c, z, hz⟩) a := by
  rw [← etaleLocalRingIsoAlong_germ_of_lift hF f hf c z hz pt hpt hfz a]
  simp

/-- A domination of geometric points of `F` is carried by a morphism `p : F ⟶ G` to a
domination of their images in `G`. -/
theorem geometricPointMap_map_value (p : F ⟶ G) {x y : GeometricPoint B S hS F}
    (f : y.val.siteObject ⟶ x.val.siteObject)
    (hf : F.map f.op x.val.value = y.val.value) :
    G.map f.op (geometricPointMap p x).val.value = (geometricPointMap p y).val.value := by
  have h := congrArg (fun k => k x.val.value) (p.naturality f.op)
  change p.app (Opposite.op y.val.siteObject) (F.map f.op x.val.value) =
    G.map f.op (p.app (Opposite.op x.val.siteObject) x.val.value) at h
  rw [hf] at h
  exact h.symm

/-- The comparison isomorphism of étale local rings of `G` along the image under `p` of a
domination of geometric points of `F`. -/
noncomputable def etaleLocalRingIsoAlongMap (hG : IsAlgebraicSpace B S hS G) (p : F ⟶ G)
    {x y : GeometricPoint B S hS F}
    (f : y.val.siteObject ⟶ x.val.siteObject)
    (hf : F.map f.op x.val.value = y.val.value) :
    etaleLocalRing B S hS G (geometricPointMap p x) ≅
      etaleLocalRing B S hS G (geometricPointMap p y) :=
  etaleLocalRingIsoAlong (x := geometricPointMap p x) (y := geometricPointMap p y) hG f
    (geometricPointMap_map_value p f hf)

/-- The inverse of `etaleLocalRingIsoAlongMap` carries the germ at the image of the dominating
point of a section on a chart back to its germ at the image of the dominated point, for any two
lifts of the points to the chart compatible with the domination. -/
theorem etaleLocalRingIsoAlongMap_inv_germ_of_lift (hG : IsAlgebraicSpace B S hS G)
    (p : F ⟶ G) {x y : GeometricPoint B S hS F}
    (f : y.val.siteObject ⟶ x.val.siteObject)
    (hf : F.map f.op x.val.value = y.val.value)
    (c : SmallEtale B S hS G)
    (z : (geometricPointMap p x).val.siteObject ⟶ c.obj.left)
    (hz : c.obj.hom.app (Opposite.op (geometricPointMap p x).val.siteObject) z =
      (geometricPointMap p x).val.value)
    (pt : (geometricPointMap p y).val.siteObject ⟶ c.obj.left)
    (hpt : c.obj.hom.app (Opposite.op (geometricPointMap p y).val.siteObject) pt =
      (geometricPointMap p y).val.value)
    (hfz : f ≫ z = pt)
    (a : (structurePresheaf B S hS G).obj (Opposite.op c)) :
    (etaleLocalRingIsoAlongMap hG p f hf).inv.hom
        (etaleLocalRingGerm B S hS G (geometricPointMap p y)
          (Opposite.op ⟨c, pt, hpt⟩) a) =
      etaleLocalRingGerm B S hS G (geometricPointMap p x)
        (Opposite.op ⟨c, z, hz⟩) a :=
  etaleLocalRingIsoAlong_inv_germ_of_lift (x := geometricPointMap p x)
    (y := geometricPointMap p y) hG f (geometricPointMap_map_value p f hf) c z hz pt hpt hfz a

/-- The homomorphism `𝒪_{G, p∘ȳ} ⟶ 𝒪_{F, ȳ}` obtained by transporting the canonical
homomorphism of étale local rings at `x` through the comparison isomorphisms is compatible with
the germ maps over `p`. -/
theorem isEtaleLocalRingMap_etaleLocalRingIsoAlong
    (hF : IsAlgebraicSpace B S hS F) (hG : IsAlgebraicSpace B S hS G) (p : F ⟶ G)
    {x y : GeometricPoint B S hS F}
    (f : y.val.siteObject ⟶ x.val.siteObject)
    (hf : F.map f.op x.val.value = y.val.value) :
    IsEtaleLocalRingMap p y
      (((etaleLocalRingIsoAlong hF f hf).hom.hom).comp
        ((etaleLocalRingMap hF p x).comp
          ((etaleLocalRingIsoAlongMap hG p f hf).inv.hom))) := by
  classical
  have hfG := geometricPointMap_map_value p f hf
  intro U V g hcomm hpoint
  obtain ⟨zU, hzU, hfzU⟩ := exists_neighborhood_map_of_dominates f hf U
  obtain ⟨zV, hzV, hfzV⟩ :=
    exists_neighborhood_map_of_dominates (F := G) (x := geometricPointMap p x)
      (y := geometricPointMap p y) f hfG V
  have hzUg : V.chart.obj.hom.app
      (Opposite.op (geometricPointMap p x).val.siteObject) (zU ≫ g) =
      (geometricPointMap p x).val.value := by
    have h := congrArg (fun α => α.app (Opposite.op x.val.siteObject) zU) hcomm
    change p.app (Opposite.op x.val.siteObject)
        (U.chart.obj.hom.app (Opposite.op x.val.siteObject) zU) =
      V.chart.obj.hom.app (Opposite.op x.val.siteObject) (zU ≫ g) at h
    rw [hzU] at h
    exact h.symm
  have hext : f ≫ (zU ≫ g) = f ≫ zV := by
    rw [← Category.assoc, hfzU, hpoint]
    exact hfzV.symm
  have hpoint₀ : zU ≫ g = zV :=
    chartLift_unique_of_comp_eq (F := G) (x := geometricPointMap p x)
      (y := geometricPointMap p y) f V (zU ≫ g) zV hzUg hzV hext
  have hmap := etaleLocalRingMap_isEtaleLocalRingMap hF p x
    (⟨U.chart, zU, hzU⟩ : SmallEtaleNeighborhood x)
    (⟨V.chart, zV, hzV⟩ : SmallEtaleNeighborhood (geometricPointMap p x)) g hcomm hpoint₀
  refine RingHom.ext fun s => ?_
  have h1 := etaleLocalRingIsoAlongMap_inv_germ_of_lift hG p f hf V.chart zV hzV
    V.point V.point_comp hfzV s
  have h2 := RingHom.congr_fun hmap s
  have h3 := etaleLocalRingIsoAlong_germ_of_lift hF f hf U.chart zU hzU
    U.point U.point_comp hfzU ((Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map g).op).hom s)
  refine h3.symm.trans ?_
  refine (congrArg (fun t => (etaleLocalRingIsoAlong hF f hf).hom.hom t) h2).trans ?_
  exact congrArg
    (fun t => (etaleLocalRingIsoAlong hF f hf).hom.hom ((etaleLocalRingMap hF p x) t)) h1.symm

/-- The canonical homomorphism of étale local rings commutes with the comparison isomorphisms
along a domination of geometric points. -/
theorem etaleLocalRingIsoAlong_comp_etaleLocalRingMap
    (hF : IsAlgebraicSpace B S hS F) (hG : IsAlgebraicSpace B S hS G) (p : F ⟶ G)
    {x y : GeometricPoint B S hS F}
    (f : y.val.siteObject ⟶ x.val.siteObject)
    (hf : F.map f.op x.val.value = y.val.value) :
    ((etaleLocalRingIsoAlong hF f hf).hom.hom).comp (etaleLocalRingMap hF p x) =
      (etaleLocalRingMap hF p y).comp ((etaleLocalRingIsoAlongMap hG p f hf).hom.hom) := by
  have key := eq_etaleLocalRingMap hF p y
    (isEtaleLocalRingMap_etaleLocalRingIsoAlong hF hG p f hf)
  refine RingHom.ext fun s => ?_
  simpa using RingHom.congr_fun key ((etaleLocalRingIsoAlongMap hG p f hf).hom.hom s)

/-- Regularity of a sequence is unchanged by an isomorphism of commutative rings. -/
theorem isRegular_map_ringEquiv {R R' : Type*} [CommRing R] [CommRing R'] (e : R ≃+* R')
    (rs : List R) :
    RingTheory.Sequence.IsRegular R rs ↔
      RingTheory.Sequence.IsRegular R' (rs.map (e : R →+* R')) := by
  refine AddEquiv.isRegular_congr (e := e.toAddEquiv) ?_
  refine List.forall₂_map_right_iff.mpr (List.forall₂_same.mpr fun c _ t => ?_)
  show e.toAddEquiv (c * t) = e c * e.toAddEquiv t
  exact e.map_mul c t

/-- Regularity of a sequence of étale local germs is unchanged along a domination of geometric
points: if the images in `𝒪_{F, x̄}` of the germs at `p ∘ x̄` of sections `a₁, …, a_r` on `N` form
a regular sequence, so do the images in `𝒪_{F, ȳ}` of their germs at `p ∘ ȳ` on the restricted
neighbourhood. -/
theorem isRegular_ofFn_etaleLocalRingMap_germ_along
    (hF : IsAlgebraicSpace B S hS F) (hG : IsAlgebraicSpace B S hS G) (p : F ⟶ G)
    {x y : GeometricPoint B S hS F}
    (f : y.val.siteObject ⟶ x.val.siteObject)
    (hf : F.map f.op x.val.value = y.val.value)
    (N : SmallEtaleNeighborhood (geometricPointMap p x)) {r : ℕ}
    (a : Fin r → (structurePresheaf B S hS G).obj (Opposite.op N.chart))
    (h : RingTheory.Sequence.IsRegular (etaleLocalRing B S hS F x)
      (List.ofFn fun i => etaleLocalRingMap hF p x
        (etaleLocalRingGerm B S hS G (geometricPointMap p x) (Opposite.op N) (a i)))) :
    RingTheory.Sequence.IsRegular (etaleLocalRing B S hS F y)
      (List.ofFn fun i => etaleLocalRingMap hF p y
        (etaleLocalRingGerm B S hS G (geometricPointMap p y)
          (Opposite.op ((neighborhoodAlong (x := geometricPointMap p x)
            (y := geometricPointMap p y) f (geometricPointMap_map_value p f hf)).obj N))
          (a i))) := by
  have hmain := (isRegular_map_ringEquiv
      ((etaleLocalRingIsoAlong hF f hf).commRingCatIsoToRingEquiv)
      (List.ofFn fun i => etaleLocalRingMap hF p x
        (etaleLocalRingGerm B S hS G (geometricPointMap p x) (Opposite.op N) (a i)))).mp h
  rw [List.map_ofFn] at hmain
  convert hmain using 3 with i
  rw [← etaleLocalRingIsoAlong_germ (x := geometricPointMap p x) (y := geometricPointMap p y)
    hG f (geometricPointMap_map_value p f hf) N (a i)]
  exact (RingHom.congr_fun (etaleLocalRingIsoAlong_comp_etaleLocalRingMap hF hG p f hf) _).symm

end AlgebraicGeometry.Space

end
