module

public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleLocalRingRegularSequence
public import StacksFrontier.AlgebraicGeometry.Spaces.StalkIndependenceOfGeometricPoint

/-!
# The étale local rings of two geometric points over the same point of the space

Let `F` be an algebraic space over a scheme `S` contained in a big fppf site and let `x`, `y` be
geometric points of `F` with `y` dominating `x`, that is with the section defining `y` the
restriction of the section defining `x` along a morphism `f` of the underlying field spectra.
Restriction of small étale neighbourhoods along `f` leaves the chart unchanged and is an initial
functor (`AlgebraicGeometry.Space.neighborhoodAlong_initial`), so the two stalk colimits agree:
the comparison homomorphism `𝒪_{F, x̄} ⟶ 𝒪_{F, ȳ}` built here is an isomorphism, and it carries
the germ at `x` of a regular function on a chart to the germ at `y` of the same function on the
same chart.

Two geometric points with the same image in `AlgebraicGeometry.Space.points` are dominated by a
common third one (`AlgebraicGeometry.Space.GeometricPoint.exists_common_extension`), so their
étale local rings are isomorphic by a germ-preserving isomorphism as well, and a sequence of germs
of regular functions is regular at one of them exactly when it is regular at the other.

## Main definitions

* `AlgebraicGeometry.Space.etaleLocalRingAlong`: the comparison `𝒪_{F, x̄} ⟶ 𝒪_{F, ȳ}` along a
  domination of geometric points, as the canonical map of colimits
  `CategoryTheory.Limits.colimit.pre` for the restriction of neighbourhoods.
* `AlgebraicGeometry.Space.etaleLocalRingEquivAlong`: the same comparison as a ring isomorphism.

## Main results

* `AlgebraicGeometry.Space.etaleLocalRingAlong_germ`: the comparison carries germs to germs.
* `AlgebraicGeometry.Space.isIso_etaleLocalRingAlong`: it is an isomorphism.
* `AlgebraicGeometry.Space.isRegular_etaleLocalRingGerm_along_iff`: a sequence of germs of
  regular functions on a chart is regular at `x` exactly when it is regular at `y`.
* `AlgebraicGeometry.Space.exists_etaleLocalRingIso_isRegular_germ_iff_of_liesOver`: for two
  geometric points with the same image there is an isomorphism of étale local rings, and on
  every chart neighbouring a common dominating point a sequence of germs is regular at one
  exactly when it is regular at the other.

## Implementation notes

The regularity statements take the neighbourhood of the dominating point as a separate argument
together with the equation identifying it, because the type of a germ depends on the chart of its
neighbourhood and so a rewrite along that equation is not type correct; supplying it as a
variable and substituting is.

## References

* [Stacks Project, Tag 00LM](https://stacks.math.columbia.edu/tag/00LM)
* [Stacks Project, Tag 04JY](https://stacks.math.columbia.edu/tag/04JY)
* [Stacks Project, Tag 04K4](https://stacks.math.columbia.edu/tag/04K4)
* [Stacks Project, Tag 04KG](https://stacks.math.columbia.edu/tag/04KG)
* [Stacks Project, Lemma 06LW](https://stacks.math.columbia.edu/tag/06LW)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

/-- A sequence is regular exactly when its image under an isomorphism of commutative rings is. -/
private theorem isRegular_map_of_ringEquiv {A A' : Type*} [CommRing A] [CommRing A']
    (e : A ≃+* A') (rs : List A) :
    RingTheory.Sequence.IsRegular A rs ↔ RingTheory.Sequence.IsRegular A' (rs.map e) :=
  have := RingHomInvPair.of_ringEquiv e
  have := RingHomInvPair.symm (↑e : A →+* A') (↑e.symm : A' →+* A)
  e.toSemilinearEquiv.isRegular_congr' rs

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-! ### The comparison along a domination of geometric points -/

/-- **The comparison of étale local rings along a domination of geometric points.**  If the
section defining `y` is the restriction of the section defining `x` along `f`, then every small
étale neighbourhood of `x` is one of `y` with the same chart
(`AlgebraicGeometry.Space.neighborhoodAlong`), so the colimit defining `𝒪_{F, x̄}` maps
canonically to the one defining `𝒪_{F, ȳ}`. -/
def etaleLocalRingAlong {x y : GeometricPoint B S hS F}
    (f : y.val.siteObject ⟶ x.val.siteObject)
    (hf : F.map f.op x.val.value = y.val.value) :
    etaleLocalRing B S hS F x ⟶ etaleLocalRing B S hS F y :=
  colimit.pre (SmallEtaleNeighborhood.sections (x := y) (liftedStructurePresheaf B S hS F))
    (neighborhoodAlong f hf).op

/-- **The comparison along a domination carries germs to germs.**  The germ at `x` of a regular
function on a chart neighbouring `x` goes to the germ at `y` of the same function on the same
chart. -/
theorem etaleLocalRingAlong_germ {x y : GeometricPoint B S hS F}
    (f : y.val.siteObject ⟶ x.val.siteObject)
    (hf : F.map f.op x.val.value = y.val.value) (U : SmallEtaleNeighborhood x)
    (a : (structurePresheaf B S hS F).obj (op U.chart)) :
    (etaleLocalRingAlong f hf).hom (etaleLocalRingGerm B S hS F x (op U) a) =
      etaleLocalRingGerm B S hS F y (op ((neighborhoodAlong f hf).obj U)) a :=
  congrArg
    (fun m : (SmallEtaleNeighborhood.sections (x := x) (liftedStructurePresheaf B S hS F)).obj
        (op U) ⟶ etaleLocalRing B S hS F y =>
      m.hom (ULift.ringEquiv.symm a))
    (colimit.ι_pre
      (SmallEtaleNeighborhood.sections (x := y) (liftedStructurePresheaf B S hS F))
      (neighborhoodAlong f hf).op (op U))

/-- **The comparison along a domination is an isomorphism.** -/
theorem isIso_etaleLocalRingAlong (hF : IsAlgebraicSpace B S hS F)
    {x y : GeometricPoint B S hS F} (f : y.val.siteObject ⟶ x.val.siteObject)
    (hf : F.map f.op x.val.value = y.val.value) :
    IsIso (etaleLocalRingAlong f hf) := by
  have : Functor.Initial (neighborhoodAlong f hf) := neighborhoodAlong_initial hF f hf
  have : Functor.Final (neighborhoodAlong f hf).op :=
    Functor.final_op_of_initial (neighborhoodAlong f hf)
  exact Functor.Final.colimit_pre_isIso (neighborhoodAlong f hf).op

/-- The comparison of étale local rings along a domination of geometric points, as a ring
isomorphism. -/
def etaleLocalRingEquivAlong (hF : IsAlgebraicSpace B S hS F)
    {x y : GeometricPoint B S hS F} (f : y.val.siteObject ⟶ x.val.siteObject)
    (hf : F.map f.op x.val.value = y.val.value) :
    etaleLocalRing B S hS F x ≃+* etaleLocalRing B S hS F y :=
  haveI := isIso_etaleLocalRingAlong hF f hf
  (asIso (etaleLocalRingAlong f hf)).commRingCatIsoToRingEquiv

/-- The ring isomorphism `etaleLocalRingEquivAlong` acts as the comparison
`etaleLocalRingAlong`. -/
@[simp]
theorem etaleLocalRingEquivAlong_apply (hF : IsAlgebraicSpace B S hS F)
    {x y : GeometricPoint B S hS F} (f : y.val.siteObject ⟶ x.val.siteObject)
    (hf : F.map f.op x.val.value = y.val.value) (a : etaleLocalRing B S hS F x) :
    etaleLocalRingEquivAlong hF f hf a = (etaleLocalRingAlong f hf).hom a :=
  rfl

/-! ### Transport of a regular sequence of germs -/

/-- **A sequence of germs of regular functions on a chart is regular at a geometric point
exactly when it is regular at a point dominating it.** -/
theorem isRegular_etaleLocalRingGerm_along_iff (hF : IsAlgebraicSpace B S hS F)
    {x y : GeometricPoint B S hS F} (f : y.val.siteObject ⟶ x.val.siteObject)
    (hf : F.map f.op x.val.value = y.val.value) (U : SmallEtaleNeighborhood x)
    (rs : List ((structurePresheaf B S hS F).obj (op U.chart))) :
    RingTheory.Sequence.IsRegular (etaleLocalRing B S hS F x)
        (rs.map (etaleLocalRingGerm B S hS F x (op U))) ↔
      RingTheory.Sequence.IsRegular (etaleLocalRing B S hS F y)
        (rs.map (etaleLocalRingGerm B S hS F y (op ((neighborhoodAlong f hf).obj U)))) := by
  refine Iff.trans
    (isRegular_map_of_ringEquiv (etaleLocalRingEquivAlong hF f hf)
      (rs.map (etaleLocalRingGerm B S hS F x (op U)))) ?_
  rw [List.map_map, show
    (⇑(etaleLocalRingEquivAlong hF f hf) ∘ ⇑(etaleLocalRingGerm B S hS F x (op U))) =
      ⇑(etaleLocalRingGerm B S hS F y (op ((neighborhoodAlong f hf).obj U))) from
    funext fun a => etaleLocalRingAlong_germ f hf U a]
  exact Iff.rfl

/-! ### Two geometric points over the same point of the space -/

/-- Germs along two small étale neighbourhoods of a geometric point with the same chart and the
same lift agree. -/
private theorem etaleLocalRingGerm_congr_point {z : GeometricPoint B S hS F}
    {c : SmallEtale B S hS F} {p q : z.val.siteObject ⟶ c.obj.left}
    {hp : c.obj.hom.app (op z.val.siteObject) p = z.val.value}
    {hq : c.obj.hom.app (op z.val.siteObject) q = z.val.value} (h : p = q) :
    etaleLocalRingGerm B S hS F z (op { chart := c, point := p, point_comp := hp }) =
      etaleLocalRingGerm B S hS F z (op { chart := c, point := q, point_comp := hq }) := by
  subst h; rfl

/-- **The étale local rings of two geometric points over the same point of the space are
isomorphic, by an isomorphism carrying germs to germs.**  The two points are dominated by a
common third one, every small étale neighbourhood of which is a neighbourhood of both; on such a
chart a sequence of germs of regular functions is regular at one of the two points exactly when
it is regular at the other. -/
theorem exists_etaleLocalRingIso_isRegular_germ_iff_of_liesOver
    (hF : IsAlgebraicSpace B S hS F) {w : points B S hS F} (x y : GeometricPoint B S hS F)
    (hx : x.LiesOver w) (hy : y.LiesOver w) :
    ∃ r : GeometricPoint B S hS F,
      Nonempty (etaleLocalRing B S hS F x ≅ etaleLocalRing B S hS F y) ∧
      ∀ N : SmallEtaleNeighborhood r,
        ∃ (px : x.val.siteObject ⟶ N.chart.obj.left)
          (py : y.val.siteObject ⟶ N.chart.obj.left)
          (hpx : N.chart.obj.hom.app (op x.val.siteObject) px = x.val.value)
          (hpy : N.chart.obj.hom.app (op y.val.siteObject) py = y.val.value),
          ∀ rs : List ((structurePresheaf B S hS F).obj (op N.chart)),
            RingTheory.Sequence.IsRegular (etaleLocalRing B S hS F x)
                (rs.map (etaleLocalRingGerm B S hS F x
                  (op { chart := N.chart, point := px, point_comp := hpx }))) ↔
              RingTheory.Sequence.IsRegular (etaleLocalRing B S hS F y)
                (rs.map (etaleLocalRingGerm B S hS F y
                  (op { chart := N.chart, point := py, point_comp := hpy }))) := by
  obtain ⟨r, ⟨fx, hfx⟩, ⟨fy, hfy⟩⟩ := GeometricPoint.exists_common_extension x y hx hy
  have := isIso_etaleLocalRingAlong hF fx hfx
  have := isIso_etaleLocalRingAlong hF fy hfy
  refine ⟨r, ⟨asIso (etaleLocalRingAlong fx hfx) ≪≫
    (asIso (etaleLocalRingAlong fy hfy)).symm⟩, fun N => ?_⟩
  obtain ⟨px, hpx, hpxN⟩ := exists_neighborhood_map_of_dominates fx hfx N
  obtain ⟨py, hpy, hpyN⟩ := exists_neighborhood_map_of_dominates fy hfy N
  refine ⟨px, py, hpx, hpy, fun rs => Iff.trans
    (isRegular_etaleLocalRingGerm_along_iff hF fx hfx
      { chart := N.chart, point := px, point_comp := hpx } rs) (Iff.trans ?_
    (isRegular_etaleLocalRingGerm_along_iff hF fy hfy
      { chart := N.chart, point := py, point_comp := hpy } rs).symm)⟩
  exact iff_of_eq (congrArg
    (fun g : (structurePresheaf B S hS F).obj (op N.chart) →+* etaleLocalRing B S hS F r =>
      RingTheory.Sequence.IsRegular (etaleLocalRing B S hS F r) (rs.map g))
    (etaleLocalRingGerm_congr_point (hpxN.trans hpyN.symm)))

end AlgebraicGeometry.Space

end
