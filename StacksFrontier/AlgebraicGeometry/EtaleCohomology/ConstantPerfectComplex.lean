module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstantCoefficients
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.EnoughGeometricPoints
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FiniteLocallyConstant
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.PullbackStalk.SitePoint
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleSitePointSupport
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.Limits
public import StacksFrontier.CategoryTheory.Sites.Point.UniverseChange
public import StacksFrontier.Homology.Perfect.Basic
public import StacksFrontier.Homology.TorAmplitude.FlatResolution

/-!
# The small étale site realized in the space of a scheme

Let `B` be a big étale site containing a scheme `S`. The small étale site of `S` is realized in
the topological space of `S` by sending an object to the open image of its structure morphism:
an étale morphism of schemes is open. Two properties of that realization are recorded here — a
family of arrows is covering exactly when the images of its sources cover, and two objects whose
images share a point carry lifts of one point of the site — together with the lift of a geometric
point to an object whose image contains it.

## Main results

* `AlgebraicGeometry.SmallEtale.ofArrows_mem_topology_iff`: a family of arrows of the small étale
  site generates a covering sieve exactly when the underlying morphisms of schemes are jointly
  surjective.
* `AlgebraicGeometry.SmallEtale.ofArrows_mem_topology_final_iff`: the same at the final object,
  read through the open images in the space of `S`.
* `AlgebraicGeometry.geometricPointFiber_nonempty_of_mem_siteEtaleImageOpen`: a geometric point
  lying over a point of the image of an object of the small étale site lifts to that object.
* `AlgebraicGeometry.exists_sitePoint_fiber_nonempty`: two objects of the small étale site whose
  images share a point of `S` carry lifts of a single point of the site, in any universe above
  that of `S`.
* `AlgebraicGeometry.hasFlatRepresentative_restrictScalars`: a bounded flat representative over
  a ring is one over an isomorphic ring after restriction of scalars.

## Implementation notes

Joint surjectivity is recorded pointwise, as `∀ x, ∃ i, x ∈ Set.range …`, with the form
`⋃ i, img (U i) = Set.univ` derived from it only at the final object, where the images are
subsets of the space of `S` and `AlgebraicGeometry.siteEtaleImageOpen` applies. Away from the
final object the image of an object lives in the space of the target, so the two spellings are
not interchangeable.

That a covering sieve is jointly surjective is read off a point of the site rather than off a
refinement of the sieve by a chosen covering family: the geometric point above the given point of
the target lifts to a member of the sieve by the joint surjectivity built into a point of the
site, and the image of that lift is the given point.

The point of the site attached to a geometric point has its fibres in the universe of `S`; the
universe lift `CategoryTheory.GrothendieckTopology.Point.ulift` raises them, and the lift of an
element of a fibre along it is `ULift.up`. The raised form is the one the module-universe
comparisons of the small étale site consume: those are stated at the module universe `u + 1` and
read fibres through `CategoryTheory.GrothendieckTopology.Point.sheafFiber`, as the
implementation notes of
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstantCoefficientStalk` record, where that
universe is identified as the one at which the trivialization chain of Tag 09BI works.

Flatness over `Λ` of a module flat over an isomorphic ring `R` is
`AlgebraicGeometry.flat_of_semilinear_equiv` applied to the identity additive isomorphism; the
ring isomorphism in the intended use is the identification of the stalk of the constant
coefficient ring sheaf with the coefficient ring, so a Tor-amplitude conclusion reached over that
stalk is read over `Λ`. The two spellings of a bounded flat representative,
`StacksDraft.TorAmplitude.HasFlatRepresentative` and
`StacksDraft.Perfect.HasFlatRepresentative`, are the same condition stated in the two namespaces
that consume it, and this statement crosses between them.

## References

* [Stacks Project, Tag 021B](https://stacks.math.columbia.edu/tag/021B)
* [Stacks Project, Tag 04HU](https://stacks.math.columbia.edu/tag/04HU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe w v u

namespace AlgebraicGeometry

attribute [local instance] HasDerivedCategory.standard

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Covering families and open images -/

/-- An arrow of the small étale site to the final object is the structure morphism of its
source. -/
theorem SmallEtale.toScheme_map_to_final {U : SmallEtale B S hS}
    (g : U ⟶ SmallEtale.final B S hS) :
    (SmallEtale.toScheme B S hS).map g = B.inclusion.map U.obj.hom := by
  simpa [SmallEtale.final] using Stacks.EtaleCohomology.toScheme_map_comp_hom B hS g

/-- **A family of arrows of the small étale site generates a covering sieve exactly when the
underlying morphisms of schemes are jointly surjective.** -/
theorem SmallEtale.ofArrows_mem_topology_iff {V : SmallEtale B S hS} {I : Type*}
    (U : I → SmallEtale B S hS) (f : ∀ i, U i ⟶ V) :
    Sieve.ofArrows U f ∈ SmallEtale.topology B S hS V ↔
      ∀ x : (SmallEtale.toScheme B S hS).obj V,
        ∃ i, x ∈ Set.range ((SmallEtale.toScheme B S hS).map (f i)) := by
  refine ⟨fun hcov x => ?_, Stacks.EtaleCohomology.ofArrows_mem_topology B hS U f⟩
  set t := GeometricPoint.ofPoint ((SmallEtale.toScheme B S hS).obj V) x
  obtain ⟨W, g, hg, y, hy⟩ := (geometricPointSitePoint B S hS
    (t.map (B.inclusion.map V.obj.hom))).jointly_surjective _ hcov
    (show (geometricPointFiber B S hS (t.map (B.inclusion.map V.obj.hom))).obj V from
      ⟨t.hom, rfl⟩)
  obtain ⟨i, a, ha⟩ := (Sieve.mem_ofArrows_iff U f g).mp hg
  refine ⟨i, (SmallEtale.toScheme B S hS).map a (y.1 default), ?_⟩
  have hy' : y.1 ≫ (SmallEtale.toScheme B S hS).map g = t.hom := congrArg Subtype.val hy
  have hx : t.hom default = x := GeometricPoint.ofPoint_liesOver _ x
  rw [ha, Functor.map_comp] at hy'
  rw [← hx, ← hy']
  simp

/-- **A family of arrows to the final object of the small étale site is covering exactly when the
open images of its sources cover `S`.** -/
theorem SmallEtale.ofArrows_mem_topology_final_iff {I : Type*} (U : I → SmallEtale B S hS)
    (f : ∀ i, U i ⟶ SmallEtale.final B S hS) :
    Sieve.ofArrows U f ∈ SmallEtale.topology B S hS (SmallEtale.final B S hS) ↔
      (⋃ i, (siteEtaleImageOpen B S hS (U i) : Set S)) = Set.univ := by
  have himg (i : I) : (siteEtaleImageOpen B S hS (U i) : Set S) =
      Set.range ((SmallEtale.toScheme B S hS).map (f i)) := by
    rw [SmallEtale.toScheme_map_to_final]
    rfl
  rw [SmallEtale.ofArrows_mem_topology_iff, Set.iUnion_eq_univ_iff]
  exact forall_congr' fun x => exists_congr fun i => (Set.ext_iff.mp (himg i) x).symm

/-! ### Points of the site above a point of the space -/

/-- A geometric point of `S` lying over a point of the open image of an object of the small
étale site lifts to that object: an étale morphism admits a factorization through any point of
its image after a separably closed base. -/
theorem geometricPointFiber_nonempty_of_mem_siteEtaleImageOpen (s : GeometricPoint S)
    (U : SmallEtale B S hS) (hs : s.hom default ∈ (siteEtaleImageOpen B S hS U : Set S)) :
    Nonempty ((geometricPointFiber B S hS s).obj U) := by
  obtain ⟨y, hy⟩ := hs
  obtain ⟨l, hl, -⟩ := Scheme.exists_fac_of_etale_of_isSepClosed
    (B.inclusion.map U.obj.hom) s.hom y hy
  exact ⟨⟨l, hl⟩⟩

/-- **Two objects of the small étale site whose open images share a point of `S` carry lifts of
one point of the site.** The point is the one attached to a geometric point above the shared
point of `S`, raised to the given universe. -/
theorem exists_sitePoint_fiber_nonempty (U V : SmallEtale B S hS) (z : S)
    (hU : z ∈ (siteEtaleImageOpen B S hS U : Set S))
    (hV : z ∈ (siteEtaleImageOpen B S hS V : Set S)) :
    ∃ p : (SmallEtale.topology B S hS).Point.{max u w},
      Nonempty (p.fiber.obj U) ∧ Nonempty (p.fiber.obj V) := by
  have hz : (GeometricPoint.ofPoint S z).hom default = z :=
    GeometricPoint.ofPoint_liesOver S z
  refine ⟨(geometricPointSitePoint B S hS (GeometricPoint.ofPoint S z)).ulift.{w}, ?_, ?_⟩ <;>
    exact (geometricPointFiber_nonempty_of_mem_siteEtaleImageOpen B S hS _ _
      (by rw [hz]; assumption)).map ULift.up

/-! ### Flat representatives across an isomorphism of coefficient rings -/

/-- A bounded flat representative of an object of the derived category of `R`-modules is a
bounded flat representative over a ring `Λ` isomorphic to `R`, after restriction of scalars
along the isomorphism. -/
theorem hasFlatRepresentative_restrictScalars {Λ : Type u} {R : Type v} [CommRing Λ] [CommRing R]
    (e : Λ ≃+* R) (M : DerivedCategory (ModuleCat.{max u v} R)) (a b : ℤ)
    (h : StacksDraft.TorAmplitude.HasFlatRepresentative.{v, u} M a b) :
    StacksDraft.Perfect.HasFlatRepresentative.{u, v}
      ((ModuleCat.restrictScalars.{max u v} e.toRingHom).mapDerivedCategory.obj M) a b := by
  obtain ⟨E, hflat, hGE, hLE, ⟨iso⟩⟩ := h
  let G := ModuleCat.restrictScalars.{max u v} e.toRingHom
  refine ⟨(G.mapHomologicalComplex (ComplexShape.up ℤ)).obj E, fun i => ?_, ?_, ?_,
    ⟨G.mapDerivedCategory.mapIso iso ≪≫ G.mapDerivedCategoryFactors.app E⟩⟩
  · exact flat_of_semilinear_equiv e (AddEquiv.refl (E.X i)) (fun _ _ => rfl)
  · rw [CochainComplex.isStrictlyGE_iff]
    exact fun i hi => G.map_isZero ((CochainComplex.isStrictlyGE_iff E a).mp hGE i hi)
  · rw [CochainComplex.isStrictlyLE_iff]
    exact fun i hi => G.map_isZero ((CochainComplex.isStrictlyLE_iff E b).mp hLE i hi)

end AlgebraicGeometry

end
