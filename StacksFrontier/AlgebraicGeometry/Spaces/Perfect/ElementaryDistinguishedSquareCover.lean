module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChartBranchCodimension
public import StacksFrontier.AlgebraicGeometry.Spaces.GeometricRepresentative
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsOfPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleAffineRefinement
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModuleShriekSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.ElementaryDistinguishedSquareLiftCounts
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.PerfectEtaleLocal
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentEtaleMorphism

/-!
# The two members of an elementary distinguished square cover the space

Let `(U ⊆ X, j : V ⟶ X)` be an elementary distinguished square of algebraic spaces over a scheme
`S`.  Every point of `|X|` lies in `|U|` or in the image of `|V|`, and the étale charts of `U` and
of `V`, composed into `X`, cover the final object of the small étale site of `X`.  Consequently
perfectness of an object of `D(𝒪_X)` can be tested on `U` and on `V`.

## Main results

* `AlgebraicGeometry.Space.SmallEtale.coversTop_of_jointlySurjective`: a family of étale charts
  of an algebraic space whose images cover its points covers the final object of its small étale
  site.
* `AlgebraicGeometry.Space.mem_range_edsOpenHom_or_mem_range_edsEtaleHom`: the points of the two
  members of an elementary distinguished square cover the points of the space.
* `AlgebraicGeometry.Space.isPerfect_of_isPerfect_edsRestrict`: **an object of `D(𝒪_X)` whose
  restrictions to `U` and to `V` are perfect is perfect.**

## Implementation notes

The covering is built exactly as in
`AlgebraicGeometry.Space.SmallEtale.coversTop_of_isSurjective`, chart by chart: for an étale
chart `W` of `X` and each member `c` of the family, the fibre product `c ×_X W` is representable,
and its projection to `W` is étale.  Joint surjectivity of those projections is Stacks 03H4,
`AlgebraicGeometry.Space.exists_point_of_isPullback_presheaf`, read through the comparison of the
points of a representable presheaf with the points of its scheme,
`AlgebraicGeometry.Space.pointsEquivScheme`.

## References

* [Stacks Project, Tag 08GM](https://stacks.math.columbia.edu/tag/08GM)
* [Stacks Project, Tag 03H4](https://stacks.math.columbia.edu/tag/03H4)
* [Stacks Project, Tag 08G5](https://stacks.math.columbia.edu/tag/08G5)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **A family of étale charts covering the points of an algebraic space covers the final object
of its small étale site.**  For an étale chart `W` the fibre products of `W` with the members of
the family are étale charts over `W` which map to members of the family; their projections to
`W` are étale, and jointly surjective by Stacks 03H4. -/
theorem SmallEtale.coversTop_of_jointlySurjective (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    {K : Type*} (c : K → SmallEtale B S hS F)
    (hc : ∀ x : points B S hS F, ∃ k,
      x ∈ Set.range (pointsMap B S hS (yoneda.obj (c k).1.left) (c k).1.hom)) :
    (SmallEtale.topology B S hS F).CoversTop c := by
  intro W
  have hrep : ∀ k, yoneda.relativelyRepresentable (c k).1.hom := fun k => (c k).property.rep
  let g := W.1.hom
  let q : ∀ k, (hrep k).pullback g ⟶ W.1.left := fun k => (hrep k).snd g
  let p : ∀ k, (hrep k).pullback g ⟶ (c k).1.left := fun k => (hrep k).fst' g
  have hw : ∀ k, yoneda.map (p k) ≫ (c k).1.hom = yoneda.map (q k) ≫ g := by
    intro k
    simp only [p, q, Functor.relativelyRepresentable.map_fst']
    exact (hrep k).w g
  have hqEtale : ∀ k, Etale ((BigFppfOver.toScheme B S hS).map (q k)) := fun k =>
    (c k).property.property g ((hrep k).fst g) ((hrep k).snd g) ((hrep k).isPullback g)
  let Vc : K → SmallEtale B S hS F := fun k =>
    ⟨CostructuredArrow.mk (yoneda.map (q k) ≫ W.1.hom),
      etale_comp_of_scheme B S hS (q k) W.1.hom (hqEtale k) W.property⟩
  let a : ∀ k, Vc k ⟶ W := fun k => ObjectProperty.homMk (CostructuredArrow.homMk (q k) rfl)
  let b : ∀ k, Vc k ⟶ c k := fun k =>
    ObjectProperty.homMk (CostructuredArrow.homMk (p k) (hw k))
  have hcov : Sieve.ofArrows Vc a ∈ SmallEtale.topology B S hS F W := by
    refine SmallEtale.ofArrows_mem_topology B S hS F Vc a ?_
    refine (Scheme.ofArrows_mem_precoverage_iff (P := @Etale)).2 ⟨fun w => ?_, hqEtale⟩
    obtain ⟨k, z, hz⟩ := hc (pointsMap B S hS (yoneda.obj W.1.left) g
      ((pointsEquivScheme B S hS W.1.left).symm w))
    obtain ⟨v, -, hv⟩ := exists_point_of_isPullback_presheaf B S hS ((hrep k).isPullback g) z
      ((pointsEquivScheme B S hS W.1.left).symm w) hz
    refine ⟨k, pointsEquivScheme B S hS _ v, ?_⟩
    apply (pointsEquivScheme B S hS W.1.left).symm.injective
    rw [← hv, ← ChartBranch.pointsEquivScheme_symm_pointsMap, Equiv.symm_apply_apply]
    rfl
  refine (SmallEtale.topology B S hS F).superset_covering ?_ hcov
  rintro Z f ⟨T, h, _, ⟨k⟩, rfl⟩
  exact ⟨k, ⟨h ≫ b k⟩⟩

section Square

variable {W : AlgebraicSpaces B S hS} {Ve : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
  {Uo : Subfunctor W.1} {fV : Ve ⟶ W.1}
  (hsq : IsElementaryDistinguishedSquare B S hS W.2 Uo fV)

/-- **The points of the two members of an elementary distinguished square cover the points of the
space.**  A point outside `|U|` is the image of a geometric point which, lying over the closed
complement, lifts along the étale morphism of the square. -/
theorem mem_range_edsOpenHom_or_mem_range_edsEtaleHom (x : points B S hS W.1) :
    x ∈ Set.range (pointsMap B S hS (edsOpen B S hS hsq).1 (edsOpenHom B S hS hsq).hom) ∨
      x ∈ Set.range (pointsMap B S hS (edsEtale B S hS hsq).1 (edsEtaleHom B S hS hsq).hom) := by
  by_cases hx : x ∈ Set.range (pointsMap B S hS Uo.toFunctor Uo.ι)
  · exact Or.inl hx
  · right
    obtain ⟨xb, rfl⟩ := exists_geometricRepresentative B S hS W.1 x
    let t : GeometricPointLift B S hS (edsEtaleHom B S hS hsq).hom xb :=
      (unique_geometricPointLift_edsEtaleHom_of_notMem B S hS hsq xb hx).default
    refine ⟨(liftGeometricPoint B S hS (edsEtaleHom B S hS hsq) t).image, ?_⟩
    rw [← geometricPointMap_image, geometricPointMap_liftGeometricPoint]

/-- The étale chart of the ambient space obtained by composing a chart of one member of an
elementary distinguished square into the space. -/
abbrev edsChart (b : Bool) : SmallEtale B S hS W.1 :=
  match b with
  | true => (smallEtalePostcomp B S hS (edsOpenHom B S hS hsq) (isEtale_edsOpenHom B S hS hsq)).obj
      (exists_surjective_smallEtale_chart B S hS (edsOpen B S hS hsq).1
        (edsOpen B S hS hsq).2).choose
  | false => (smallEtalePostcomp B S hS (edsEtaleHom B S hS hsq)
      (isEtale_edsEtaleHom B S hS hsq)).obj
      (exists_surjective_smallEtale_chart B S hS (edsEtale B S hS hsq).1
        (edsEtale B S hS hsq).2).choose

/-- **Two charts of the members of an elementary distinguished square cover the space**: a chart
of the open subspace surjective on points and a chart of the étale space surjective on points,
both composed into the space. -/
theorem coversTop_edsChart :
    (SmallEtale.topology B S hS W.1).CoversTop (edsChart B S hS hsq) := by
  refine SmallEtale.coversTop_of_jointlySurjective B S hS W.1 _ fun x => ?_
  rcases mem_range_edsOpenHom_or_mem_range_edsEtaleHom B S hS hsq x with ⟨y, rfl⟩ | ⟨y, rfl⟩
  · obtain ⟨z, rfl⟩ := (exists_surjective_smallEtale_chart B S hS (edsOpen B S hS hsq).1
      (edsOpen B S hS hsq).2).choose_spec y
    exact ⟨true, z, congrFun (pointsMap_comp B S hS _ _ (edsOpenHom B S hS hsq).hom) z⟩
  · obtain ⟨z, rfl⟩ := (exists_surjective_smallEtale_chart B S hS (edsEtale B S hS hsq).1
      (edsEtale B S hS hsq).2).choose_spec y
    exact ⟨false, z, congrFun (pointsMap_comp B S hS _ _ (edsEtaleHom B S hS hsq).hom) z⟩

/-- The two members of an elementary distinguished square, the open subspace at `true` and the
étale space at `false`. -/
abbrev edsCoverMember : Bool → AlgebraicSpaces B S hS
  | true => edsOpen B S hS hsq
  | false => edsEtale B S hS hsq

/-- The morphisms from the two members of an elementary distinguished square to the space. -/
abbrev edsCoverMemberHom : (b : Bool) → edsCoverMember B S hS hsq b ⟶ W
  | true => edsOpenHom B S hS hsq
  | false => edsEtaleHom B S hS hsq

/-- The morphisms from the two members of an elementary distinguished square to the space are
étale. -/
theorem isEtale_edsCoverMemberHom : (b : Bool) → IsEtale B S hS (edsCoverMemberHom B S hS hsq b).hom
  | true => isEtale_edsOpenHom B S hS hsq
  | false => isEtale_edsEtaleHom B S hS hsq

attribute [local instance] HasDerivedCategory.standard etaleModulePullback_additive
  preservesFiniteLimits_etaleModulePullback preservesFiniteColimits_etaleModulePullback
  smallEtaleRingedSite_hasSheafify smallEtaleRingedSite_wEqualsLocallyBijective

/-- **Perfectness on an elementary distinguished square is tested on its two members.**  An
object `E` of `D(𝒪_X)` whose restrictions to `U` and to `V` are perfect is perfect.

This is `AlgebraicGeometry.Space.isPerfect_of_forall_isPerfect_etaleModulePullback` for the
family of the two members, whose charts cover the space by
`AlgebraicGeometry.Space.coversTop_edsChart`. -/
theorem isPerfect_of_isPerfect_edsRestrict (E : DerivedCategory (Modules.{u, u} B S hS W.1 W.2))
    (hU : (smallEtaleRingedSite B S hS (edsOpen B S hS hsq).1 (edsOpen B S hS hsq).2).IsPerfect
      ((etaleModulePullback B S hS (edsOpenHom B S hS hsq)
        (isEtale_edsOpenHom B S hS hsq)).mapDerivedCategory.obj E))
    (hV : (smallEtaleRingedSite B S hS (edsEtale B S hS hsq).1 (edsEtale B S hS hsq).2).IsPerfect
      ((etaleModulePullback B S hS (edsEtaleHom B S hS hsq)
        (isEtale_edsEtaleHom B S hS hsq)).mapDerivedCategory.obj E)) :
    (smallEtaleRingedSite B S hS W.1 W.2).IsPerfect E := by
  refine isPerfect_of_forall_isPerfect_etaleModulePullback B S hS (edsCoverMember B S hS hsq)
    (edsCoverMemberHom B S hS hsq) (isEtale_edsCoverMemberHom B S hS hsq) ?_ E ?_
  · intro U
    refine (SmallEtale.topology B S hS W.1).superset_covering ?_ (coversTop_edsChart B S hS hsq U)
    rintro Z g ⟨_ | _, ⟨k⟩⟩
    · exact ⟨⟨false, _⟩, ⟨k⟩⟩
    · exact ⟨⟨true, _⟩, ⟨k⟩⟩
  · rintro (_ | _)
    exacts [hV, hU]

end Square

end AlgebraicGeometry.Space

end
