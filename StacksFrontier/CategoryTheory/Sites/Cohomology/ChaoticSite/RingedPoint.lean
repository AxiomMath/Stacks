module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.FibredCategory.RingedProjection
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ChaoticSite.PointMorphism
import StacksCore.Tactic.StacksAttribute

/-!
# The ringed point of a chaotic site

Let `C` be a category with its chaotic topology and let `B` be a commutative ring. The one-object
site `*` with the ring `B` on it is a ringed site, and the unique functor `C ⥤ *` is a fibred
category, so the data of [Stacks, Tag 08P8] applies: the topology `C` inherits from `*` is again
the chaotic one, the induced morphism of topoi is the point morphism
`Stacks.ChaoticSite.pointMorphism`, and the inverse-image structure sheaf
is the constant sheaf of rings written `B` with an underline in the source. The morphism of
ringed topoi `(Sh(C), B) ⟶ (Sh(*), B)` is then the `ringedProjection` of 08P8 applied to this
situation, which is why it is registered here rather than constructed again.

## Main definitions

* `Stacks.ChaoticSite.RingedPointSituation`: a category and a ring on the point.
* `Stacks.ChaoticSite.RingedPointSituation.fibredSituation`: its instance of the fibred-category
  situation of Stacks 08P8.
* `Stacks.ChaoticSite.RingedPointSituation.pointRingSheaf`: the constant sheaf of commutative
  rings `B` on the point.
* `Stacks.ChaoticSite.RingedPointSituation.constantRingSheaf`: the inverse-image structure sheaf
  on `C`, the source's `B` with an underline.

## Main results

* `Stacks.ChaoticSite.pointFunctor_isFibered`: the projection of any category to the one-object
  category is a fibred category.
* `Stacks.ChaoticSite.RingedPointSituation.topology_eq_trivial`: the topology inherited from the
  chaotic point is the chaotic topology.
* `Stacks.ChaoticSite.RingedPointSituation.projection_eq_pointMorphism`: the morphism of topoi
  underlying the ringed projection is the point morphism.

## Implementation notes

`Stacks.ChaoticSite.RingedPointSituation` is not to be confused with
`Stacks.Sheaves.RingedPoint.RingedPointSituation`: that one is a point of an arbitrary ringed
topos together with the identification `O_p = p⁻¹O`, whereas this one is the much smaller datum
of a category and a ring, from which the point of the chaotic topos on it is constructed. They
are different objects and neither subsumes the other.

The morphism of ringed topoi itself is not redefined here: it is
`Stacks.Sites.FibredCategory.FibredCategorySituation.ringedProjection` applied to
`fibredSituation`, as the source's construction prescribes.

`projection_eq_pointMorphism` is an `HEq` rather than an `Eq` because the two morphisms of topoi
live over topologies that are equal but not syntactically identical — `fibredSituation.topology`
and `GrothendieckTopology.trivial C` — so their types differ until `topology_eq_trivial` is used
to identify them. The proof generalizes the topology, rewrites it along that equality, and then
the two morphisms are definitionally equal: both are assembled from
`Functor.sheafPushforwardContinuous`, `Functor.sheafPushforwardCocontinuous` and
`Functor.sheafAdjunctionCocontinuous` for the same functor. The structure
`ProjectionData` has four fields
(`hom`, `inverseImage_eq`, `pushforward_eq`, `adjunction_eq`), and the proof destructures it
accordingly.

The coefficient universe `max w u v` is the one Stacks 08P8 forces: the morphism of topoi is
formed on sheaves of sets valued in a universe containing both the site and the one-object base.

## References

* [Stacks Project, Tag 08PF](https://stacks.math.columbia.edu/tag/08PF)
* [Stacks Project, Tag 08P8](https://stacks.math.columbia.edu/tag/08P8)
-/

@[expose] public noncomputable section

open CategoryTheory

namespace Stacks.ChaoticSite

universe w v u

/-- The projection of any category to the one-object category is a fibred category: every
morphism of the base is an identity, and an identity lifts to an identity, which is strongly
cartesian because it is an isomorphism. -/
@[stacks 08PF "ringed_point"]
instance pointFunctor_isFibered (C : Type u) [Category.{v} C] :
    (Functor.star C).IsFibered := by
  apply Functor.IsFibered.of_exists_isStronglyCartesian
  intro a R f
  obtain rfl : R = (Functor.star C).obj a := Subsingleton.elim _ _
  obtain rfl : f = 𝟙 _ := Subsingleton.elim _ _
  let _ : (Functor.star C).IsHomLift (𝟙 _) (𝟙 a) := IsHomLift.id rfl
  exact ⟨a, 𝟙 a, Functor.IsStronglyCartesian.of_isIso
    (p := Functor.star C) (f := 𝟙 _) (φ := 𝟙 a)⟩

/-- A category with its chaotic topology and a ring on the point. -/
@[stacks 08PF "ringed_point"]
structure RingedPointSituation where
  /-- The underlying category. -/
  C : Type u
  /-- Morphisms of the underlying category. -/
  [category : Category.{v} C]
  /-- The coefficient ring, carried on the point. -/
  B : CommRingCat.{max w u v}

attribute [instance] RingedPointSituation.category

namespace RingedPointSituation

variable (s : RingedPointSituation.{w, v, u})

/-- The constant sheaf of commutative rings `B` on the point. Every presheaf on the one-object
site is a sheaf for the chaotic topology, so this is just the constant presheaf. -/
def pointRingSheaf :
    Sheaf (GrothendieckTopology.trivial (Discrete PUnit.{u + 1}))
      CommRingCat.{max w u v} :=
  (sheafBotEquivalence (C := Discrete PUnit.{u + 1}) CommRingCat.{max w u v}).inverse.obj
    ((Functor.const (Discrete PUnit.{u + 1})ᵒᵖ).obj s.B)

/-- The fibred-category situation of Stacks 08P8 obtained from the unique functor to the ringed
point. -/
@[stacks 08PF "ringed_point"]
def fibredSituation :
    Stacks.Sites.FibredCategory.FibredCategorySituation.{u, u, u, v, max w u v} where
  base :=
    { C := Discrete PUnit.{u + 1}
      J := GrothendieckTopology.trivial (Discrete PUnit.{u + 1})
      O := s.pointRingSheaf }
  C := s.C
  p := Functor.star s.C

/-- The universe lift that Stacks 08P8 applies to the base structure sheaf does not change it:
`ULift B` is `B` as a commutative ring. -/
def pointRingSheafLiftIso :
    s.fibredSituation.liftedBaseSheaf ≅ s.pointRingSheaf :=
  (fullyFaithfulSheafToPresheaf _ _).preimageIso <| NatIso.ofComponents
    (fun U ↦ (ULift.ringEquiv : ULift (s.pointRingSheaf.obj.obj U) ≃+*
      s.pointRingSheaf.obj.obj U).toCommRingCatIso)
    (by intro U V f; ext x; rfl)

/-- The inverse-image structure sheaf on the chaotic site: the source's `B` with an underline. -/
abbrev constantRingSheaf := s.fibredSituation.totalRingedTopos.O

/-- **Stacks 08PF.** The topology that `C` inherits from the chaotic point is the chaotic
topology. -/
@[stacks 08PF "ringed_point"]
theorem topology_eq_trivial :
    s.fibredSituation.topology = GrothendieckTopology.trivial s.C := by
  rw [GrothendieckTopology.trivial_eq_bot]
  apply le_antisymm
  · show (s.fibredSituation.p.inheritedTopology s.fibredSituation.base.J) ≤
      (⊥ : GrothendieckTopology s.fibredSituation.C)
    rw [Functor.inheritedTopology_eq]
    apply (Precoverage.toGrothendieck_le_iff_le_toPrecoverage).2
    intro X R hR
    show Sieve.generate R ∈ (⊥ : GrothendieckTopology s.fibredSituation.C) X
    rw [GrothendieckTopology.bot_covering]
    let p := s.fibredSituation.p
    have hbase : Sieve.generate (R.map p) = ⊤ :=
      GrothendieckTopology.trivial_covering.1 ((GrothendieckTopology.mem_toPrecoverage_iff
        (GrothendieckTopology.trivial (Discrete PUnit.{u + 1})) (R.map p)).mp hR.2)
    have hid : Sieve.generate (R.map p) (𝟙 (p.obj X)) := by
      rw [hbase]
      trivial
    rcases hid with ⟨Y, a, gBase, hgBase, hag⟩
    obtain ⟨Z, hZY, g, hg, hmap⟩ := (Presieve.map_iff (F := p) (R := R)).1 hgBase
    let _ : p.IsStronglyCartesian (p.map g) g := hR.1 g hg
    have : IsIso (p.map g) := by
      show IsIso (𝟙 _)
      infer_instance
    have : IsIso g := Functor.IsStronglyCartesian.isIso_of_base_isIso p (p.map g) g
    exact Sieve.generate_of_contains_isSplitEpi (R := R) g hg
  · exact bot_le

/-- The morphism of topoi assembled from the canonical restriction, its right adjoint and their
adjunction is the point morphism, as soon as the topology on the source is the chaotic one. The
topology is taken as a variable so that it, and with it the continuity instances that depend on
it, can be substituted along the equality; this avoids carrying the two
instances as fields of `ProjectionData`. -/
private theorem heq_pointMorphism_of_eq {D : Type u} [Category.{v} D]
    (J : GrothendieckTopology D)
    [(Functor.star D).IsContinuous J (GrothendieckTopology.trivial (Discrete PUnit.{u + 1}))]
    [(Functor.star D).IsCocontinuous J (GrothendieckTopology.trivial (Discrete PUnit.{u + 1}))]
    (hJ : J = GrothendieckTopology.trivial D)
    (m : MorphismOfTopoi (Sheaf J (Type (max w u v)))
      (Sheaf (GrothendieckTopology.trivial (Discrete PUnit.{u + 1})) (Type (max w u v))))
    (hi : m.inverseImage = (Functor.star D).sheafPushforwardContinuous
      (Type (max w u v)) J (GrothendieckTopology.trivial (Discrete PUnit.{u + 1})))
    (hp : m.pushforward = (Functor.star D).sheafPushforwardCocontinuous
      (Type (max w u v)) J (GrothendieckTopology.trivial (Discrete PUnit.{u + 1})))
    (ha : HEq m.adj ((Functor.star D).sheafAdjunctionCocontinuous
      (Type (max w u v)) J (GrothendieckTopology.trivial (Discrete PUnit.{u + 1})))) :
    HEq m (pointMorphism.{max w u v, v, u} D) := by
  subst hJ
  cases m with
  | mk pushforward inverseImage adj finite =>
    subst hi hp
    cases ha
    rfl

/-- **Stacks 08PF.** The morphism of topoi underlying the ringed projection is the point
morphism of the chaotic site. -/
@[stacks 08PF "ringed_point"]
theorem projection_eq_pointMorphism :
    HEq s.fibredSituation.projection (pointMorphism.{max w u v, v, u} s.C) := by
  have hc : (Functor.star s.fibredSituation.C).IsContinuous s.fibredSituation.topology
      (GrothendieckTopology.trivial (Discrete PUnit.{u + 1})) :=
    s.fibredSituation.isContinuous
  have hcc : (Functor.star s.fibredSituation.C).IsCocontinuous s.fibredSituation.topology
      (GrothendieckTopology.trivial (Discrete PUnit.{u + 1})) :=
    s.fibredSituation.isCocontinuous
  exact heq_pointMorphism_of_eq s.fibredSituation.topology s.topology_eq_trivial
    s.fibredSituation.inducedProjection.hom
    s.fibredSituation.inducedProjection.inverseImage_eq
    s.fibredSituation.inducedProjection.pushforward_eq
    s.fibredSituation.inducedProjection.adjunction_eq

end RingedPointSituation

end Stacks.ChaoticSite

/- The morphism of ringed topoi of Stacks 08PF is not a new construction: it is the
`ringedProjection` of Stacks 08P8 applied to `fibredSituation`, so the tag is registered on that
declaration rather than on a copy of it. -/
add_to_stacks 08PF "ringed_point"
  Stacks.Sites.FibredCategory.FibredCategorySituation.ringedProjection
