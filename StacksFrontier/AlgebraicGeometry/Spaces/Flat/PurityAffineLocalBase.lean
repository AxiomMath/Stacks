module

public import StacksFrontier.AlgebraicGeometry.Spaces.Flat.PurityEtaleMorphism
public import StacksFrontier.AlgebraicGeometry.Spaces.RelationSize
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints

/-!
# Affine local bases for a pre-pure situation

`AlgebraicGeometry.Space.PrePureSituation.IsAffineLocalAt` asks of a situation of Stacks 0CV6
that its base be represented by a scheme of the site isomorphic to the spectrum of a local
ring and that the chosen point be closed for the point topology of Stacks 03BY. Part (2) of
Stacks 0CW3 and the transfer step of Stacks 0CW4 are both stated over such a base; this file
constructs one.

The construction is the base change to the spectrum of a local ring of the base. Concretely,
for a point `v` of a scheme `V` of the site:

* `AlgebraicGeometry.BigFppfOver.specStalk` is `Spec 𝒪_{V, v}` as an object of the big fppf
  site over `S` — it is contained in the site by
  `AlgebraicGeometry.BigFppfSite.contains_of_mono`, because `Spec 𝒪_{V, v} ⟶ V` is a
  preimmersion and hence a monomorphism;
* `AlgebraicGeometry.BigFppfOver.specStalkTo` is the canonical morphism to `V`, realizing
  `AlgebraicGeometry.Scheme.fromSpecStalk` in the site; and
* `AlgebraicGeometry.BigFppfOver.specStalkClosedPoint` is the closed point, which is closed
  for the point topology by
  `AlgebraicGeometry.BigFppfOver.isClosed_singleton_specStalkClosedPoint`.

Feeding this into `AlgebraicGeometry.Space.PointedOver` gives
`AlgebraicGeometry.Space.PrePureSituation.specStalkPointedOver`, a morphism of pointed
algebraic spaces into the base of the situation whose base change is affine local at its
chosen point
(`AlgebraicGeometry.Space.PrePureSituation.isAffineLocalAt_specStalkPointedOver`).

Because the base of a situation of Stacks 0CV6 is an algebraic space it has a scheme atlas,
which is surjective on points by Stacks 03BZ, so the chart `V` and the point `v` above the
chosen point of the base are always available. The existence statement
`AlgebraicGeometry.Space.PrePureSituation.exists_pointedOver_isAffineLocalAt` therefore carries
no hypothesis at all: *every* situation of Stacks 0CV6 admits a pointed base change whose base
is affine local at its chosen point.

## Implementation notes

The local ring produced here is `𝒪_{V, v}` for an étale chart `V` of the base, which is a local
ring of the base in the sense of Stacks 04KG only after passage to a strict henselization.
Nothing here henselizes: `AlgebraicGeometry.Space.PrePureSituation.IsAffineLocalAt` does not
ask for it, and neither does Stacks 0CW3 part (2).

## References

* [Stacks Project, Tag 0CW3](https://stacks.math.columbia.edu/tag/0CW3)
* [Stacks Project, Tag 0CW4](https://stacks.math.columbia.edu/tag/0CW4)
* [Stacks Project, Tag 03BY](https://stacks.math.columbia.edu/tag/03BY)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

namespace BigFppfOver

attribute [local instance] Space.pointTopology

/-- **The spectrum of a stalk of an object of the site is again an object of the site.** -/
theorem contains_spec_stalk (V : BigFppfOver B S hS)
    (v : (BigFppfOver.toScheme B S hS).obj V) :
    B.Contains (Spec (((BigFppfOver.toScheme B S hS).obj V).presheaf.stalk v)) :=
  B.contains_of_mono (((BigFppfOver.toScheme B S hS).obj V).fromSpecStalk v) V.left.property

/-- **`Spec 𝒪_{V, v}` as an object of the big fppf site over `S`**, for a point `v` of a scheme
`V` of the site. It is contained in the site by
`AlgebraicGeometry.BigFppfOver.contains_spec_stalk`, and its structure morphism to `S` is that
of `V` precomposed with `AlgebraicGeometry.Scheme.fromSpecStalk`. -/
noncomputable def specStalk (V : BigFppfOver B S hS)
    (v : (BigFppfOver.toScheme B S hS).obj V) : BigFppfOver B S hS :=
  Over.mk ((B.inclusion.preimage (((BigFppfOver.toScheme B S hS).obj V).fromSpecStalk v) :
    B.obj (contains_spec_stalk B S hS V v) ⟶ V.left) ≫ V.hom)

/-- **The canonical morphism `Spec 𝒪_{V, v} ⟶ V` in the big fppf site over `S`.** -/
noncomputable def specStalkTo (V : BigFppfOver B S hS)
    (v : (BigFppfOver.toScheme B S hS).obj V) : specStalk B S hS V v ⟶ V :=
  Over.homMk (B.inclusion.preimage (((BigFppfOver.toScheme B S hS).obj V).fromSpecStalk v)) rfl

/-- The underlying morphism of schemes of `AlgebraicGeometry.BigFppfOver.specStalkTo` is
`AlgebraicGeometry.Scheme.fromSpecStalk`. -/
theorem toScheme_map_specStalkTo (V : BigFppfOver B S hS)
    (v : (BigFppfOver.toScheme B S hS).obj V) :
    (BigFppfOver.toScheme B S hS).map (specStalkTo B S hS V v) =
      ((BigFppfOver.toScheme B S hS).obj V).fromSpecStalk v :=
  B.inclusion.map_preimage _

/-- **The closed point of `Spec 𝒪_{V, v}`**, as a point of the represented presheaf in the
sense of Stacks 03BY. -/
noncomputable def specStalkClosedPoint (V : BigFppfOver B S hS)
    (v : (BigFppfOver.toScheme B S hS).obj V) :
    Space.points B S hS (yoneda.obj (specStalk B S hS V v)) :=
  (Space.pointsEquivScheme B S hS (specStalk B S hS V v)).symm
    (IsLocalRing.closedPoint (((BigFppfOver.toScheme B S hS).obj V).presheaf.stalk v))

/-- `AlgebraicGeometry.BigFppfOver.specStalkClosedPoint` is the closed point of
`Spec 𝒪_{V, v}` under the comparison bijection of Stacks 03BV. -/
@[simp]
theorem pointsToScheme_specStalkClosedPoint (V : BigFppfOver B S hS)
    (v : (BigFppfOver.toScheme B S hS).obj V) :
    Space.pointsToScheme B S hS (specStalk B S hS V v)
        (specStalkClosedPoint B S hS V v) =
      IsLocalRing.closedPoint (((BigFppfOver.toScheme B S hS).obj V).presheaf.stalk v) :=
  (Space.pointsEquivScheme B S hS (specStalk B S hS V v)).apply_symm_apply _

/-- The comparison bijection for `V` carries the image of a point of `Spec 𝒪_{V, v}` to the image
of its scheme point under `AlgebraicGeometry.Scheme.fromSpecStalk`. -/
private theorem pointsToScheme_pointsMap_specStalkTo_eq (V : BigFppfOver B S hS)
    (v : (BigFppfOver.toScheme B S hS).obj V)
    (t : Space.points B S hS (yoneda.obj (specStalk B S hS V v))) :
    Space.pointsToScheme B S hS V (Space.pointsMap B S hS
        (yoneda.obj (specStalk B S hS V v)) (yoneda.map (specStalkTo B S hS V v)) t) =
      ((BigFppfOver.toScheme B S hS).obj V).fromSpecStalk v
        (Space.pointsToScheme B S hS (specStalk B S hS V v) t) := by
  rw [Space.pointsToScheme_pointsMap_yoneda, toScheme_map_specStalkTo]
  rfl

/-- **The closed point of `Spec 𝒪_{V, v}` lies above `v`.** -/
theorem pointsToScheme_pointsMap_specStalkTo (V : BigFppfOver B S hS)
    (v : (BigFppfOver.toScheme B S hS).obj V) :
    Space.pointsToScheme B S hS V (Space.pointsMap B S hS
        (yoneda.obj (specStalk B S hS V v)) (yoneda.map (specStalkTo B S hS V v))
        (specStalkClosedPoint B S hS V v)) = v := by
  rw [pointsToScheme_pointsMap_specStalkTo_eq, pointsToScheme_specStalkClosedPoint]
  exact Scheme.fromSpecStalk_closedPoint

/-- **Every point of `V` specializing to `v` is the image of a point of `Spec 𝒪_{V, v}`.** The
range of `Spec 𝒪_{V, v} ⟶ V` is the set of points specializing to `v`, by
`AlgebraicGeometry.Scheme.range_fromSpecStalk`; this reads that range through the comparison
bijection of Stacks 03BV, so that the preimage is a point of the represented presheaf. -/
theorem exists_pointsMap_specStalkTo_eq (V : BigFppfOver B S hS)
    (v : (BigFppfOver.toScheme B S hS).obj V)
    {v' : (BigFppfOver.toScheme B S hS).obj V} (hv' : v' ⤳ v) :
    ∃ t : Space.points B S hS (yoneda.obj (specStalk B S hS V v)),
      Space.pointsToScheme B S hS V (Space.pointsMap B S hS
          (yoneda.obj (specStalk B S hS V v)) (yoneda.map (specStalkTo B S hS V v)) t) = v' := by
  obtain ⟨z, hz⟩ : v' ∈ Set.range (((BigFppfOver.toScheme B S hS).obj V).fromSpecStalk v) :=
    Scheme.range_fromSpecStalk.ge hv'
  refine ⟨(Space.pointsEquivScheme B S hS (specStalk B S hS V v)).symm z, ?_⟩
  rw [pointsToScheme_pointsMap_specStalkTo_eq, ← hz]
  exact congrArg _ ((Space.pointsEquivScheme B S hS (specStalk B S hS V v)).apply_symm_apply z)

/-- **Every point of `Spec 𝒪_{V, v}` maps to a point of `V` specializing to `v`.** -/
theorem specializes_pointsToScheme_pointsMap_specStalkTo (V : BigFppfOver B S hS)
    (v : (BigFppfOver.toScheme B S hS).obj V)
    (t : Space.points B S hS (yoneda.obj (specStalk B S hS V v))) :
    Space.pointsToScheme B S hS V (Space.pointsMap B S hS
        (yoneda.obj (specStalk B S hS V v)) (yoneda.map (specStalkTo B S hS V v)) t) ⤳ v := by
  rw [pointsToScheme_pointsMap_specStalkTo_eq]
  exact Scheme.range_fromSpecStalk.le ⟨_, rfl⟩

/-- **The closed point of `Spec 𝒪_{V, v}` is closed for the point topology** of Stacks 03BY. -/
theorem isClosed_singleton_specStalkClosedPoint (V : BigFppfOver B S hS)
    (v : (BigFppfOver.toScheme B S hS).obj V) :
    IsClosed ({specStalkClosedPoint B S hS V v} :
      Set (Space.points B S hS (yoneda.obj (specStalk B S hS V v)))) := by
  rw [Space.isClosed_pointTopology_yoneda_iff_isClosed_image, Set.image_singleton,
    pointsToScheme_specStalkClosedPoint]
  exact IsLocalRing.isClosed_singleton_closedPoint _

end BigFppfOver

namespace Space

attribute [local instance] pointTopology

variable {B S hS}

/-- **The pointed base change of a situation of Stacks 0CV6 to `Spec 𝒪_{V, v}`.** Given a
scheme `V` of the site with a morphism `a : V ⟶ Y` to the base and a point `v` of `V` above the
chosen point `y`, this is the morphism of pointed algebraic spaces
`(Spec 𝒪_{V, v}, 𝔪) ⟶ (Y, y)` obtained by composing
`AlgebraicGeometry.BigFppfOver.specStalkTo` with `a`. -/
noncomputable def PrePureSituation.specStalkPointedOver (P : PrePureSituation.{u, u} B S hS)
    (V : BigFppfOver B S hS) (a : yoneda.obj V ⟶ P.Y)
    (v : points B S hS (yoneda.obj V))
    (hv : pointsMap B S hS (yoneda.obj V) a v = P.y) : PointedOver P where
  Y' := yoneda.obj (BigFppfOver.specStalk B S hS V (pointsToScheme B S hS V v))
  hY' := isAlgebraicSpace_yoneda B S hS _
  g := yoneda.map (BigFppfOver.specStalkTo B S hS V (pointsToScheme B S hS V v)) ≫ a
  y' := BigFppfOver.specStalkClosedPoint B S hS V (pointsToScheme B S hS V v)
  mapsPoint := by
    rw [pointsMap_comp, Function.comp_apply]
    refine .trans (congrArg (pointsMap B S hS (yoneda.obj V) a) ?_) hv
    exact injective_pointsToScheme B S hS V
      (BigFppfOver.pointsToScheme_pointsMap_specStalkTo B S hS V _)

/-- **The base change of a situation of Stacks 0CV6 to `Spec 𝒪_{V, v}` is affine local at its
chosen point.** Its base is `Spec 𝒪_{V, v}`, represented by the object
`AlgebraicGeometry.BigFppfOver.specStalk` of the site, and the stalk is a local ring; its
chosen point is the closed point, which is closed for the point topology by
`AlgebraicGeometry.BigFppfOver.isClosed_singleton_specStalkClosedPoint`. -/
theorem PrePureSituation.isAffineLocalAt_specStalkPointedOver
    (P : PrePureSituation.{u, u} B S hS) (V : BigFppfOver B S hS) (a : yoneda.obj V ⟶ P.Y)
    (v : points B S hS (yoneda.obj V))
    (hv : pointsMap B S hS (yoneda.obj V) a v = P.y) :
    (P.specStalkPointedOver V a v hv).baseChange.IsAffineLocalAt :=
  ⟨⟨BigFppfOver.specStalk B S hS V (pointsToScheme B S hS V v),
      ((BigFppfOver.toScheme B S hS).obj V).presheaf.stalk (pointsToScheme B S hS V v),
      inferInstance, ⟨Iso.refl _⟩, ⟨Iso.refl _⟩⟩,
    BigFppfOver.isClosed_singleton_specStalkClosedPoint B S hS V _⟩

/-- **Every situation of Stacks 0CV6 admits a pointed base change whose base is affine local at
its chosen point.** -/
theorem PrePureSituation.exists_pointedOver_isAffineLocalAt
    (P : PrePureSituation.{u, u} B S hS) :
    ∃ c : PointedOver P, c.baseChange.IsAffineLocalAt := by
  obtain ⟨V, a, hsurj, -⟩ := P.hY.exists_atlas
  obtain ⟨v, hv⟩ := (surjective_iff_surjective_pointsMap B S hS P.Y P.hY V a).1 hsurj P.y
  exact ⟨_, P.isAffineLocalAt_specStalkPointedOver V a v hv⟩

end Space

end AlgebraicGeometry

end
