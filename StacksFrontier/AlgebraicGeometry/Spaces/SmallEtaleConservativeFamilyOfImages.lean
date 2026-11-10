module

public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleStalkExactness
public import StacksFrontier.AlgebraicGeometry.Spaces.StalkIndependenceOfGeometricPoint

/-!
# Conservative families of geometric points meeting every point

The geometric points of an algebraic space `X` are a conservative family of points of its small
étale site (Stacks 04K5).  Since the stalk at a geometric point only depends on the point of `|X|`
it lies over (Stacks 04K4), any family of geometric points that meets every point of `|X|` is
already conservative.

## Main results

* `AlgebraicGeometry.Space.isConservativeFamilyOfPoints_etaleSitePoint_of_forall_image`: a family
  of geometric points of an algebraic space meeting every point of the space is a conservative
  family of points of its small étale site.

## References

* [Stacks Project, Tag 04K5](https://stacks.math.columbia.edu/tag/04K5)
* [Stacks Project, Tag 04K4](https://stacks.math.columbia.edu/tag/04K4)
* [Stacks Project, Tag 00YK](https://stacks.math.columbia.edu/tag/00YK)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Space

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hX : IsAlgebraicSpace B S hS X)

/-- **A family of geometric points meeting every point of an algebraic space is a conservative
family of points of its small étale site.**  If every geometric point of `X` lies over the same
point of `|X|` as some member of the family `p`, then the points of the small étale site attached
to the members of `p` are a conservative family. -/
theorem isConservativeFamilyOfPoints_etaleSitePoint_of_forall_image {t : Type*}
    (p : t → GeometricPoint B S hS X)
    (hp : ∀ x : GeometricPoint B S hS X, ∃ k, (p k).image = x.image) :
    ObjectProperty.IsConservativeFamilyOfPoints
      (ObjectProperty.ofObj (fun k : t => etaleSitePoint B S hS X (p k) hX)) := by
  apply ObjectProperty.IsConservativeFamilyOfPoints.mk'
  intro U R hR
  apply smallEtale_sieve_of_pointwise_covering B S hS X U R
  intro z
  obtain ⟨x, q, z', hz⟩ := exists_geo_lift_at_chart_point B S hS X U z
  obtain ⟨k, hk⟩ := hp x
  obtain ⟨r, ⟨fx, hfx⟩, ⟨fy, hfy⟩⟩ :=
    GeometricPoint.exists_common_extension (x := x.image) x (p k) rfl hk
  let N : SmallEtaleNeighborhood r :=
    { chart := U
      point := fx ≫ q.1
      point_comp := (NatTrans.naturality_apply U.obj.hom fx.op q.1).trans
        ((congrArg (X.map fx.op) q.2).trans hfx) }
  obtain ⟨w, hw, hcomp⟩ := exists_neighborhood_map_of_dominates fy hfy N
  obtain ⟨V, g, hg, q', hq'⟩ := hR ⟨etaleSitePoint B S hS X (p k) hX,
    ObjectProperty.ofObj_apply (fun k : t => etaleSitePoint B S hS X (p k) hX) k⟩ ⟨w, hw⟩
  obtain ⟨ρ⟩ : Nonempty ((BigFppfOver.toScheme B S hS).obj r.val.siteObject) :=
    inferInstanceAs (Nonempty (Spec (CommRingCat.of r.val.carrier)))
  have : Subsingleton ((BigFppfOver.toScheme B S hS).obj x.val.siteObject) :=
    inferInstanceAs (Subsingleton (Spec (CommRingCat.of x.val.carrier)))
  refine ⟨V, g, hg, (BigFppfOver.toScheme B S hS).map q'.val
    ((BigFppfOver.toScheme B S hS).map fy ρ), ?_⟩
  have hm : q'.val ≫ (SmallEtale.toOver B S hS X).map g = w := congrArg Subtype.val hq'
  rw [← Scheme.Hom.comp_apply, ← Functor.map_comp, hm, ← Scheme.Hom.comp_apply,
    ← Functor.map_comp, hcomp]
  change (BigFppfOver.toScheme B S hS).map (fx ≫ q.1) ρ = z
  rwa [Functor.map_comp, Scheme.Hom.comp_apply, Subsingleton.elim
    ((BigFppfOver.toScheme B S hS).map fx ρ) z']

end AlgebraicGeometry.Space

end
