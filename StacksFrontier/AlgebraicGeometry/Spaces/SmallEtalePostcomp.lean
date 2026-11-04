module

public import StacksFrontier.AlgebraicGeometry.Spaces.Category
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.StructureSheaf

/-!
# Postcomposition of étale charts along an étale morphism

Let `f : X ⟶ Y` be an étale morphism of algebraic spaces over a scheme `S` contained in a big
fppf site `B`.  If `φ : yoneda.obj U ⟶ X` is an étale chart of `X`, then `φ ≫ f` is an étale
chart of `Y`, by the very definition of étaleness of `f`.  This assignment is functorial and
leaves the underlying scheme and the underlying scheme morphisms unchanged; it is the
postcomposition functor between the small étale sites of `X` and `Y`.

## Main definitions

* `AlgebraicGeometry.Space.smallEtalePostcomp` is the postcomposition functor from the small
  étale site of `X` to that of `Y`.

## Main results

* `AlgebraicGeometry.Space.smallEtalePostcomp_obj_hom` and
  `AlgebraicGeometry.Space.smallEtalePostcomp_map_left` record its action on charts and on
  morphisms of charts.
* `AlgebraicGeometry.Space.smallEtalePostcomp_isContinuous`: postcomposition is continuous for
  the two small étale topologies, so restriction along it carries sheaves to sheaves.

## Implementation notes

The functor is the lift to the étale charts of `Y` of postcomposition on scheme charts,
`CategoryTheory.CostructuredArrow.map`; the hypothesis that the lift lands in the étale charts
is `AlgebraicGeometry.Space.IsEtale` applied to the chart, in that definition's own binder
order.  Taking the lift rather than constructing the functor by hand makes
`AlgebraicGeometry.Space.SmallEtale.toOver` — and hence everything computed from the underlying
object of the big fppf site — strictly invariant: `smallEtalePostcomp_comp_toOver` is `rfl`.

## References

* [Stacks Project, Tag 03LP](https://stacks.math.columbia.edu/tag/03LP)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : AlgebraicSpaces B S hS}

/-- Postcomposition of an étale scheme chart with an étale morphism of algebraic spaces, as a
functor between the small étale sites.  Its underlying scheme and scheme morphisms are
unchanged. -/
@[stacks 03LP "the postcomposition functor"]
def smallEtalePostcomp (f : X ⟶ Y) (hf : IsEtale B S hS f.hom) :
    SmallEtale B S hS X.1 ⥤ SmallEtale B S hS Y.1 :=
  (IsEtaleChart B S hS Y.1).lift
    (SmallEtale.inclusion B S hS X.1 ⋙ CostructuredArrow.map f.hom)
    (fun U ↦ hf _ U.1.hom U.2)

/-- On charts, postcomposition replaces `U ⟶ X` by its composite with `f`. -/
@[stacks 03LP "action on charts"]
theorem smallEtalePostcomp_obj_hom (f : X ⟶ Y) (hf : IsEtale B S hS f.hom)
    (U : SmallEtale B S hS X.1) :
    ((smallEtalePostcomp B S hS f hf).obj U).1.hom = U.1.hom ≫ f.hom := rfl

/-- On chart morphisms, postcomposition leaves the underlying scheme map unchanged. -/
@[stacks 03LP "action on chart morphisms"]
theorem smallEtalePostcomp_map_left (f : X ⟶ Y) (hf : IsEtale B S hS f.hom)
    {U V : SmallEtale B S hS X.1} (g : U ⟶ V) :
    ((smallEtalePostcomp B S hS f hf).map g).hom.left = g.hom.left := rfl

/-- Postcomposition leaves the underlying object of the big fppf site of `S` unchanged, on
charts and on morphisms of charts at once. -/
theorem smallEtalePostcomp_comp_toOver (f : X ⟶ Y) (hf : IsEtale B S hS f.hom) :
    smallEtalePostcomp B S hS f hf ⋙ SmallEtale.toOver B S hS Y.1 =
      SmallEtale.toOver B S hS X.1 := rfl

/-- Postcomposition preserves fibre products of étale charts: the fibre product of charts is
detected on the underlying objects of the big fppf site of `S`, which postcomposition leaves
unchanged. -/
instance smallEtalePostcomp_preservesPullbacks (f : X ⟶ Y) (hf : IsEtale B S hS f.hom) :
    PreservesLimitsOfShape WalkingCospan (smallEtalePostcomp B S hS f hf) :=
  have : ReflectsLimitsOfShape WalkingCospan (SmallEtale.toOver B S hS Y.1) := inferInstance
  have : PreservesLimitsOfShape WalkingCospan
      (smallEtalePostcomp B S hS f hf ⋙ SmallEtale.toOver B S hS Y.1) := by
    change PreservesLimitsOfShape WalkingCospan (SmallEtale.toOver B S hS X.1)
    infer_instance
  preservesLimitsOfShape_of_reflects_of_preserves _ (SmallEtale.toOver B S hS Y.1)

/-- A covering family of étale charts of `X` is carried by postcomposition to a covering family
of étale charts of `Y`: the covering condition only sees the underlying objects of `Sch_κ`,
which postcomposition leaves unchanged. -/
theorem precoverage_le_comap_smallEtalePostcomp (f : X ⟶ Y) (hf : IsEtale B S hS f.hom) :
    SmallEtale.precoverage B S hS X.1 ≤
      (SmallEtale.topology B S hS Y.1).toPrecoverage.comap
        (smallEtalePostcomp B S hS f hf) := by
  intro U R hR
  obtain ⟨E, rfl, hE⟩ := hR
  rw [Precoverage.mem_comap_iff, GrothendieckTopology.mem_toPrecoverage_iff,
    ← PreZeroHypercover.presieve₀_map]
  exact Precoverage.generate_mem_toGrothendieck ⟨E.map (smallEtalePostcomp B S hS f hf), rfl, hE⟩

/-- Postcomposition along an étale morphism of algebraic spaces is continuous for the small
étale topologies, so that restriction along it carries sheaves on the small étale site of `Y`
to sheaves on that of `X`. -/
@[stacks 03LP "continuity"]
instance smallEtalePostcomp_isContinuous (f : X ⟶ Y) (hf : IsEtale B S hS f.hom) :
    (smallEtalePostcomp B S hS f hf).IsContinuous
      (SmallEtale.topology B S hS X.1) (SmallEtale.topology B S hS Y.1) :=
  Stacks.Sites.isContinuous_toGrothendieck_of_le_comap _ _ _
    (precoverage_le_comap_smallEtalePostcomp B S hS f hf)

end AlgebraicGeometry.Space

end
