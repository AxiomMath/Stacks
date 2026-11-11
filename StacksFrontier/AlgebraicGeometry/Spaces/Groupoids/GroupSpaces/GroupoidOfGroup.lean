module

public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupActions
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupoidOfSliceObject
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupoidOverField
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.Quotient.RestrictionFieldExtension

/-!
# The groupoid `(B, G, p, p, m)` of a group algebraic space

Let `(G, m)` be a group algebraic space over an algebraic space `B`, with structure morphism
`p : G ⟶ B`.  Then `(B, G, p, p, m)` is a groupoid in algebraic spaces over `B`: its object space
is `B`, its arrow space is `G`, its source and its target are both `p`, and its composition is
the group law `m : G ×_B G ⟶ G`.  This is Lemma 0444 for the trivial action of `G` on `B`, and
over the spectrum of a field it is the groupoid of Stacks 06DZ, in the situation of Stacks 06DX.

## Main definitions

* `Deformation.GroupoidObject.ofGrpObj`: the groupoid object of a group object of a cartesian
  monoidal category, with the unit as object of objects, the group as object of arrows, both
  source and target the unique morphism to the unit, and composition the multiplication.
* `AlgebraicGeometry.Space.groupoidOfGroup`: the groupoid in algebraic spaces `(B, G, p, p, m)`
  over `B` of a group algebraic space `G` over `B`.
* `AlgebraicGeometry.Space.groupoidOfGroupOverField`: **Stacks 06DZ**, the groupoid
  `(Spec k, G, p, p, m)` over `Spec k` of a group algebraic space over a field `k`.
* `AlgebraicGeometry.Space.groupoidOverFieldOfGroup`: the same groupoid, as an instance of the
  situation of Stacks 06DY.

## Main results

* `AlgebraicGeometry.Space.groupoidOfGroup_objects`, `groupoidOfGroup_arrows`,
  `groupoidOfGroup_source`, `groupoidOfGroup_target` and `groupoidOfGroup_comp`: the five pieces
  of the quintuple are `B`, `G`, `p`, `p` and `m`, the last read through the canonical comparison
  of the fibre product of `p` with itself taken in presheaves with the one taken over `B`.

## References

* [Stacks Project, Tag 06DZ](https://stacks.math.columbia.edu/tag/06DZ)
* [Stacks Project, Tag 06DX](https://stacks.math.columbia.edu/tag/06DX)
* [Stacks Project, Tag 06DY](https://stacks.math.columbia.edu/tag/06DY)
* [Stacks Project, Tag 0444](https://stacks.math.columbia.edu/tag/0444)
* [Stacks Project, Tag 043W](https://stacks.math.columbia.edu/tag/043W)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace Deformation.GroupoidObject

universe v u

variable {D : Type u} [Category.{v} D] [CartesianMonoidalCategory D] (G : D) [GrpObj G]

/-- A morphism into `G ⊗ G` followed by the multiplication is the product of its two
components in the group of morphisms into `G`. -/
theorem comp_mul_eq_mul {X : D} (k : X ⟶ G ⊗ G) :
    k ≫ μ[G] =
      (k ≫ CartesianMonoidalCategory.fst G G) * (k ≫ CartesianMonoidalCategory.snd G G) := by
  rw [Hom.mul_def]
  congr 1
  ext <;> simp

/-- **The groupoid object of a group object.** A group object `G` of a cartesian monoidal
category is a groupoid object with one object: the object of objects is the unit, the object of
arrows is `G`, the source and the target are both the unique morphism to the unit, the object of
composable pairs is `G ⊗ G` and the composition is the multiplication `μ`; the identity is the
unit `η` and the inverse is `ι`. -/
def ofGrpObj [HasPullback (CartesianMonoidalCategory.snd G G) (CartesianMonoidalCategory.fst G G)] :
    GroupoidObject D where
  objects := 𝟙_ D
  arrows := G
  pairs := G ⊗ G
  triples := pullback (CartesianMonoidalCategory.snd G G) (CartesianMonoidalCategory.fst G G)
  source := toUnit G
  target := toUnit G
  identity := η[G]
  inverse := ι[G]
  fst := CartesianMonoidalCategory.fst G G
  snd := CartesianMonoidalCategory.snd G G
  isPullback_pairs := IsPullback.of_is_product' (tensorProductIsBinaryProduct G G)
    isTerminalTensorUnit
  comp := μ[G]
  fst₃ := pullback.fst _ _
  snd₃ := pullback.snd _ _
  isPullback_triples := IsPullback.of_hasPullback _ _
  identity_source := toUnit_unique _ _
  identity_target := toUnit_unique _ _
  inverse_source := toUnit_unique _ _
  inverse_target := toUnit_unique _ _
  comp_source := toUnit_unique _ _
  comp_target := toUnit_unique _ _
  comp_identity_left a k h₁ h₂ := by
    rw [comp_mul_eq_mul, h₁, h₂, ← Category.assoc, toUnit_unique (a ≫ toUnit G) (toUnit _),
      ← Hom.one_def, one_mul]
  comp_identity_right a k h₁ h₂ := by
    rw [comp_mul_eq_mul, h₁, h₂, ← Category.assoc, toUnit_unique (a ≫ toUnit G) (toUnit _),
      ← Hom.one_def, mul_one]
  comp_inverse_left a k h₁ h₂ := by
    rw [comp_mul_eq_mul, h₁, h₂, ← Hom.inv_def, inv_mul_cancel, Hom.one_def,
      ← Category.assoc, toUnit_unique (a ≫ toUnit G) (toUnit _)]
  comp_inverse_right a k h₁ h₂ := by
    rw [comp_mul_eq_mul, h₁, h₂, ← Hom.inv_def, mul_inv_cancel, Hom.one_def,
      ← Category.assoc, toUnit_unique (a ≫ toUnit G) (toUnit _)]
  comp_assoc k l m n hkl hm₁ hm₂ hn₁ hn₂ := by
    rw [comp_mul_eq_mul, comp_mul_eq_mul _ n, hm₁, hm₂, hn₁, hn₂, comp_mul_eq_mul,
      comp_mul_eq_mul, hkl, mul_assoc]

end Deformation.GroupoidObject

universe u

namespace AlgebraicGeometry.Space

variable {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
  {B : (BigFppfOver C S hS)ᵒᵖ ⥤ Type u} {hB : IsAlgebraicSpace C S hS B}

/-- **The groupoid `(B, G, p, p, m)` of a group algebraic space.** For a group algebraic space
`(G, m)` over an algebraic space `B`, with structure morphism `p : G ⟶ B`, the groupoid in
algebraic spaces over `B` whose object space is `B`, whose arrow space is `G`, whose source and
target are both `p`, and whose composition is the group law `m`. -/
def groupoidOfGroup (G : GroupAlgebraicSpace C S hS B hB) :
    GroupoidInAlgebraicSpaces C S hS ⟨B, hB⟩ :=
  letI : GrpObj G.obj.X := G.obj.grp
  GroupoidInAlgebraicSpaces.ofOverGroupoidObject ⟨B, hB⟩
    (Deformation.GroupoidObject.ofGrpObj G.obj.X) hB G.property

variable (G : GroupAlgebraicSpace C S hS B hB)

/-- The object space of `groupoidOfGroup G` is the base `B`. -/
theorem groupoidOfGroup_objects : (groupoidOfGroup G).objects = ⟨B, hB⟩ := rfl

/-- The arrow space of `groupoidOfGroup G` is `G`. -/
theorem groupoidOfGroup_arrows : (groupoidOfGroup G).arrows = ⟨G.obj.X.left, G.property⟩ := rfl

/-- The source of `groupoidOfGroup G` is the structure morphism `p : G ⟶ B`. -/
theorem groupoidOfGroup_source :
    (groupoidOfGroup G).source.hom = G.obj.X.hom := rfl

/-- The target of `groupoidOfGroup G` is the structure morphism `p : G ⟶ B`. -/
theorem groupoidOfGroup_target :
    (groupoidOfGroup G).target.hom = G.obj.X.hom := rfl

/-- The composition of `groupoidOfGroup G` is the group law `m : G ×_B G ⟶ G`, read on the fibre
product of `p` with itself taken in presheaves through the canonical comparison with the one taken
over `B`, which commutes with both projections
(`AlgebraicGeometry.GroupoidInAlgebraicSpaces.overPairsComparison_fst` and
`AlgebraicGeometry.GroupoidInAlgebraicSpaces.overPairsComparison_snd`). -/
theorem groupoidOfGroup_comp :
    letI : GrpObj G.obj.X := G.obj.grp
    (groupoidOfGroup G).comp.hom =
      GroupoidInAlgebraicSpaces.overPairsComparison ⟨B, hB⟩
        (Deformation.GroupoidObject.ofGrpObj G.obj.X) ≫ μ[G.obj.X].left := rfl

/-- The comparison through which the composition of `groupoidOfGroup G` is the group law is the
lift of the two projections: its composites with the two projections of `G ×_B G` are the two
projections of the fibre product of `p` with itself taken in presheaves. -/
theorem groupoidOfGroup_overPairsComparison :
    letI : GrpObj G.obj.X := G.obj.grp
    GroupoidInAlgebraicSpaces.overPairsComparison ⟨B, hB⟩
        (Deformation.GroupoidObject.ofGrpObj G.obj.X) ≫ (fst G.obj.X G.obj.X).left =
      pullback.fst G.obj.X.hom G.obj.X.hom ∧
    GroupoidInAlgebraicSpaces.overPairsComparison ⟨B, hB⟩
        (Deformation.GroupoidObject.ofGrpObj G.obj.X) ≫ (snd G.obj.X G.obj.X).left =
      pullback.snd G.obj.X.hom G.obj.X.hom :=
  letI : GrpObj G.obj.X := G.obj.grp
  ⟨GroupoidInAlgebraicSpaces.overPairsComparison_fst _ _,
    GroupoidInAlgebraicSpaces.overPairsComparison_snd _ _⟩

/-! ### The situation of Stacks 06DX -/

variable {k : Type u} [Field k] (hk : C.Contains (Spec (.of k))) (structureMap : Spec (.of k) ⟶ S)

/-- **Stacks 06DZ.** In the situation of Stacks 06DX — a scheme `S`, a field `k` over `S` and a
group algebraic space `(G, m)` over `Spec k` — the quintuple `(Spec k, G, p, p, m)`, where
`p : G ⟶ Spec k` is the structure morphism, is a groupoid in algebraic spaces over `Spec k`.
Its five pieces are identified by `AlgebraicGeometry.Space.groupoidOfGroup_objects`,
`groupoidOfGroup_arrows`, `groupoidOfGroup_source`, `groupoidOfGroup_target` and
`groupoidOfGroup_comp`. -/
@[stacks 06DZ "the groupoid `(Spec k, G, p, p, m)` over `Spec k` of a group over a field"]
abbrev groupoidOfGroupOverField
    (G : GroupAlgebraicSpace C S hS (fieldSpace C hS hk structureMap).obj
      (fieldSpace C hS hk structureMap).property) :
    GroupoidInAlgebraicSpaces C S hS (fieldSpace C hS hk structureMap) :=
  groupoidOfGroup G

/-- The groupoid `(Spec k, G, p, p, m)` of Stacks 06DZ is in the situation of Stacks 06DY: its
object space is the spectrum of the field `k`. -/
def groupoidOverFieldOfGroup
    (G : GroupAlgebraicSpace C S hS (fieldSpace C hS hk structureMap).obj
      (fieldSpace C hS hk structureMap).property) :
    GroupoidOverField C S hS (fieldSpace C hS hk structureMap) where
  carrier := k
  containsSpec := hk
  structureMap := structureMap
  groupoid := groupoidOfGroupOverField hk structureMap G
  objects_eq := rfl

end AlgebraicGeometry.Space
