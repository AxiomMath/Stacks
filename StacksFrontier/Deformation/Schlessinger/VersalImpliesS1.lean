module

public import StacksFrontier.Deformation.Predeformation.Basic
public import StacksFrontier.Deformation.FormalObject.Basic
public import StacksFrontier.Deformation.FormalObject.RestrictionEquivalence
public import StacksFrontier.Deformation.FormalObject.VersalLifting
public import StacksFrontier.Deformation.Formal.VersalObject.MapsToFormalObject
public import StacksFrontier.Deformation.Schlessinger.Basic
public import StacksFrontier.Deformation.Smooth.Versal
public import StacksFrontier.Deformation.Groupoid.BaseCategory
import StacksCore.Tactic.StacksAttribute

/-!
# Factoring through a lift in a category cofibered in groupoids

Existence and uniqueness of the morphism filling in a triangle whose base triangle commutes,
for a category cofibered in groupoids.

## Main results

* `Deformation.cofibered_factor` produces the fill-in.
* `Deformation.existsUnique_factor_of_isHomLift`, of
  `StacksFrontier.Deformation.SchlessingerConditions.CofiberedLifts`, says it is unique.

## Implementation notes

Both are read off the fibered-in-groupoids unique-lifting property of the opposite functor and
transported back along `Quiver.Hom.unop`.

The proof of **Stacks 06SY**, together with the formal-object pushforward and strictification
machinery it is built from, is in `StacksFrontier/Deformation/Schlessinger/Basic.lean`.

## References

* [Stacks Project, Tag 06SY](https://stacks.math.columbia.edu/tag/06SY)
-/
@[expose] public section

open CategoryTheory
open IsLocalRing

namespace Deformation

universe u v w uF vF

/-- In a category cofibered in groupoids, a map `i : z ⟶ y` and a map `a : z ⟶ x` whose base
maps factor as `p.map i ≫ s = p.map a` are joined by a morphism `y ⟶ x` lying over `s`. -/
lemma cofibered_factor
    {F : Type uF} [Category.{vF} F] {C : Type u} [Category.{v} C]
    (p : F ⥤ C) (hp : IsCofiberedInGroupoids p)
    {z y x : F} (i : z ⟶ y) (a : z ⟶ x)
    (s : p.obj y ⟶ p.obj x) (ha : p.map i ≫ s = p.map a) :
    ∃ b : y ⟶ x, p.map b = s ∧ i ≫ b = a := by
  have hcomm : s.op ≫ p.op.map i.op = p.op.map a.op := by
    show (p.map i ≫ s).op = (p.map a).op
    exact congrArg Quiver.Hom.op ha
  obtain ⟨b, ⟨hb, hfac⟩, _⟩ := hp.unique_lift i.op a.op s.op hcomm
  exact ⟨b.unop, congrArg Quiver.Hom.unop hb, congrArg Quiver.Hom.unop hfac⟩

end Deformation

end
