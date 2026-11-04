module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupoidOverField
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.More.UnibranchArrowsMinimalPrimePairs
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.More.UnibranchArrowsTensorSquare
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.Stabilizer.ActionGroupoid
public import StacksFrontier.AlgebraicGeometry.Spaces.UnibranchTransport

/-!
# Geometrically unibranch arrow spaces of groupoids and of groups over a field

Let `(U, R, s, t, c)` be a groupoid in algebraic spaces whose object space is the spectrum of a
field `k`.  Then `R` is geometrically unibranch, and so is every group algebraic space over a
field, the latter being the arrow space of the groupoid attached to the trivial action of the
group on the base.

## Main definitions

* `AlgebraicGeometry.Space.baseFieldSpace`: the spectrum of a field, as the base algebraic space
  over itself.
* `AlgebraicGeometry.Space.trivialActionGroupoid`: the action groupoid of the trivial action of a
  group algebraic space over a field on the base.

## Main results

* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.isGeometricallyUnibranch_arrows_of_splitAtIds`:
  **Stacks 06E4**, the groupoid case, for a groupoid presented by an equality of object spaces.
* `AlgebraicGeometry.GroupoidOverField.isGeometricallyUnibranch_arrows`: **Stacks 06E4**, the
  groupoid case, for the situation of [Stacks Project, Tag 06DY].
* `AlgebraicGeometry.Space.isGeometricallyUnibranch_groupAlgebraicSpace`: **Stacks 06E4**, the
  group case, the situation of [Stacks Project, Tag 06DX].

## Implementation notes

The proof follows the source.  The reductions of
`AlgebraicGeometry.GroupoidInAlgebraicSpaces.isGeometricallyUnibranch_arrows_of_minimalPrimesSplit`
pass to the restrictions of the groupoid along the algebraically closed extensions of the base
field (Tags 06E2, 06E1 and 06DQ), to the identity arrow (Tag 06E3) and to a single geometric
point, and use flatness of the composition law (Tag 06E0).  What remains is
[Stacks Project, Tag 06DU] for the étale local rings `A = 𝒪_{R, e}` and
`C = 𝒪_{R ×_{s, U, t} R, (e, e)}` of each such restriction, which is
`AlgebraicGeometry.GroupoidInAlgebraicSpaces.minimalPrimesSplitAtIdentityArrow_restriction`:
`C` is weakly étale over `A ⊗_k A` through the two projections
(`AlgebraicGeometry.Space.cartesian_etaleStalk_tensor_weaklyEtale`) and strictly henselian, hence
a strict henselization of the localization of `A ⊗_k A` at `𝔪_A ⊗ A + A ⊗ 𝔪_A`.

The groupoid case is stated twice: once for a groupoid together with an equality identifying its
object space with the algebraic space of the spectrum of a field, and once for
`AlgebraicGeometry.GroupoidOverField`, the bundled form of the situation of Tag 06DY.  The
bundled form phrases that identification through `AlgebraicGeometry.schemeSpace` while the
reductions phrase it through `AlgebraicGeometry.Space.fieldSpace`; the two are the same term, so
`AlgebraicGeometry.GroupoidOverField.objects_eq_fieldSpace` is the identity proof.

The group case goes through the action groupoid of the trivial action of the group on the base,
as the constant dimension of a group over a field does: the object space of that groupoid is the
base, its arrow space is `G ×_{Spec k} Spec k`, and both its source and its target are the
structure morphism of `G`.  The first projection identifies that arrow space with `G`, and
geometric unibranchness is carried along an isomorphism of algebraic spaces by
`AlgebraicGeometry.Space.isGeometricallyUnibranch_of_isIso`.

Two choices keep the elaboration of the group case cheap.  The base is taken to be
`AlgebraicGeometry.Space.baseFieldSpace`, the algebraic space of the spectrum of the field,
rather than the final algebraic space over that spectrum: the two are the same algebraic space,
but with the former the identification of the object space of the action groupoid with the
spectrum of the field is immediate, while with the latter it unfolds through the terminal object
of the site.

## References

* [Stacks Project, Tag 06E4](https://stacks.math.columbia.edu/tag/06E4)
* [Stacks Project, Tag 06DU](https://stacks.math.columbia.edu/tag/06DU)
* [Stacks Project, Tag 06DX](https://stacks.math.columbia.edu/tag/06DX)
* [Stacks Project, Tag 06DY](https://stacks.math.columbia.edu/tag/06DY)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory

universe u

namespace AlgebraicGeometry

/-! ### The groupoid case -/

namespace GroupoidInAlgebraicSpaces

variable {S : Scheme.{u}} (C : BigFppfSite.{u}) (hS : C.Contains S) {k : Type u} [Field k]
  (hk : C.Contains (Spec (.of k))) (structureMap : Spec (.of k) ⟶ S)
  {B : AlgebraicSpaces C S hS} (G : GroupoidInAlgebraicSpaces C S hS B)
  (hU : G.objects = Space.fieldSpace C hS hk structureMap)

include hU in
/-- **Stacks 06E4, the groupoid case.**  The arrow space of a groupoid in algebraic spaces whose
object space is the spectrum of a field is geometrically unibranch.

The last step of the source proof is [Stacks Project, Tag 06DU] for the étale local rings
`𝒪_{R, e}` and `𝒪_{R ×_{s, U, t} R, (e, e)}` of each restriction of the groupoid along an
algebraically closed extension of the field; it is
`AlgebraicGeometry.GroupoidInAlgebraicSpaces.minimalPrimesSplitAtIdentityArrow_restriction`. -/
@[stacks 06E4 "groupoid case, for a groupoid whose object space is the spectrum of a field"]
theorem isGeometricallyUnibranch_arrows_of_splitAtIds :
    Space.IsGeometricallyUnibranch C S hS G.arrows.obj :=
  isGeometricallyUnibranch_arrows_of_minimalPrimesSplit C hS hk structureMap G hU
    fun _ _ alg' i hk' =>
      minimalPrimesSplitAtIdentityArrow_restriction C hS hk structureMap G hU alg' hk' i

end GroupoidInAlgebraicSpaces

/-! ### The groupoid case in the situation of Tag 06DY -/

namespace GroupoidOverField

variable {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
  {B : AlgebraicSpaces C S hS}

/-- The identification of the object space of the situation of [Stacks Project, Tag 06DY], read
through `AlgebraicGeometry.Space.fieldSpace`.  The two descriptions of the algebraic space of the
spectrum of the field are the same term. -/
theorem objects_eq_fieldSpace (G : GroupoidOverField C S hS B) :
    G.groupoid.objects = Space.fieldSpace C hS G.containsSpec G.structureMap :=
  G.objects_eq

/-- **Stacks 06E4, the groupoid case.**  In the situation of [Stacks Project, Tag 06DY] — a
groupoid in algebraic spaces `(U, R, s, t, c)` whose object space `U` is the spectrum of a field
`k` — the arrow space `R` is geometrically unibranch. -/
@[stacks 06E4 "groupoid case, in the situation 06DY"]
theorem isGeometricallyUnibranch_arrows (G : GroupoidOverField C S hS B) :
    Space.IsGeometricallyUnibranch C S hS G.arrows.obj :=
  GroupoidInAlgebraicSpaces.isGeometricallyUnibranch_arrows_of_splitAtIds C hS
    G.containsSpec G.structureMap G.groupoid G.objects_eq_fieldSpace

end GroupoidOverField

/-! ### The group case -/

namespace Space

/-- A fibre product along an identity is the other factor, through the first projection. -/
private noncomputable def pullbackAlongIdIso {D : Type*} [Category D] {A T : D} (f : A ⟶ T)
    [HasPullback f (𝟙 T)] : pullback f (𝟙 T) ≅ A where
  hom := pullback.fst f (𝟙 T)
  inv := pullback.lift (𝟙 A) f (by rw [Category.id_comp, Category.comp_id])
  hom_inv_id := by
    refine pullback.hom_ext ?_ ?_
    · rw [Category.assoc, pullback.lift_fst, Category.comp_id, Category.id_comp]
    · rw [Category.assoc, pullback.lift_snd, Category.id_comp]
      exact pullback.condition.trans (Category.comp_id _)
  inv_hom_id := by rw [pullback.lift_fst]

/-- The spectrum of a field, as the base algebraic space over itself.  This is the base over
which a group algebraic space in the situation of [Stacks Project, Tag 06DX] lives. -/
noncomputable abbrev baseFieldSpace {k : Type u} [Field k] (C : BigFppfSite.{u})
    (hk : C.Contains (Spec (.of k))) : AlgebraicSpaces C (Spec (.of k)) hk :=
  fieldSpace C hk hk (𝟙 (Spec (.of k)))

attribute [local instance] ModObj.trivialAction

variable {k : Type u} [Field k] (C : BigFppfSite.{u}) (hk : C.Contains (Spec (.of k)))
  (G : GroupAlgebraicSpace C (Spec (.of k)) hk (baseFieldSpace C hk).obj
    (baseFieldSpace C hk).property)

/-- The action groupoid of the trivial action of a group algebraic space over a field on the
base.  Its object space is the base, its arrow space is `G ×_{Spec k} Spec k`, and both its
source and its target are the structure morphism of the group. -/
noncomputable abbrev trivialActionGroupoid :
    ActionGroupoidConstruction (baseFieldSpace C hk) G.obj.X
      (𝟙_ (Over (baseFieldSpace C hk).obj)) G.property (baseFieldSpace C hk).property :=
  groupoidOfAction (baseFieldSpace C hk) G.obj.X (𝟙_ (Over (baseFieldSpace C hk).obj))
    G.property (baseFieldSpace C hk).property

/-- The object space of the action groupoid of the trivial action is the spectrum of the field:
the unit of the monoidal structure on the slice over the base is the base itself. -/
theorem trivialActionGroupoid_objects_eq :
    (trivialActionGroupoid C hk G).groupoid.objects = fieldSpace C hk hk (𝟙 (Spec (.of k))) :=
  (trivialActionGroupoid C hk G).objects_eq

/-- **Stacks 06E4, the group case.**  A group algebraic space over a field is geometrically
unibranch.

A group `G` over `Spec k` is the arrow space of a groupoid in algebraic spaces whose object space
is `Spec k`: the group acts trivially on the base, and the arrow space of the resulting action
groupoid is `G ×_{Spec k} Spec k`, which the first projection identifies with `G`. -/
@[stacks 06E4 "group case, in the situation 06DX"]
theorem isGeometricallyUnibranch_groupAlgebraicSpace :
    IsGeometricallyUnibranch C (Spec (.of k)) hk G.obj.X.left := by
  have harr : IsAlgebraicSpace C (Spec (.of k)) hk
      (pullback G.obj.X.hom (𝟙 (baseFieldSpace C hk).obj)) :=
    isAlgebraicSpace_pullback C (Spec (.of k)) hk G.obj.X.hom
      (𝟙 (baseFieldSpace C hk).obj) G.property (baseFieldSpace C hk).property
      (baseFieldSpace C hk).property
  have hgpd : IsGeometricallyUnibranch C (Spec (.of k)) hk
      (trivialActionGroupoid C hk G).groupoid.arrows.obj :=
    GroupoidInAlgebraicSpaces.isGeometricallyUnibranch_arrows_of_splitAtIds C hk hk
      (𝟙 (Spec (.of k))) (trivialActionGroupoid C hk G).groupoid
      (trivialActionGroupoid_objects_eq C hk G)
  have hars : pullback G.obj.X.hom (𝟙 (baseFieldSpace C hk).obj) =
      (trivialActionGroupoid C hk G).groupoid.arrows.obj :=
    (congrArg (fun Z : AlgebraicSpaces C (Spec (.of k)) hk => Z.obj)
      (trivialActionGroupoid C hk G).arrows_eq).symm
  have hpb : IsGeometricallyUnibranch C (Spec (.of k)) hk
      (pullback G.obj.X.hom (𝟙 (baseFieldSpace C hk).obj)) := by
    rw [hars]; exact hgpd
  exact isGeometricallyUnibranch_of_isIso C (Spec (.of k)) hk harr G.property
    (pullbackAlongIdIso G.obj.X.hom).hom hpb

end Space

end AlgebraicGeometry

end
