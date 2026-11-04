module
public import StacksFrontier.AlgebraicGeometry.Flatness.Flattening.Compactifications
import all StacksFrontier.AlgebraicGeometry.Flatness.Flattening.Compactifications

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Basic
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import StacksCore.Tactic.StacksAttribute

/-!
# Compactifications of morphisms of schemes

For a morphism of schemes `f : Y ⟶ S` and a compactification of `Y` over `S`, the composite of
the immersion of `Y` with the structure morphism of the compactification is `f`.

## Main results

* `AlgebraicGeometry.CompactificationOf.immersion_toBase_general`: the structure morphism of a
  compactification restricts to `f` on the interior.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

namespace CompactificationOf

variable {S : Scheme.{u}} {X : Over S}

/-- The structure morphism of a compactification restricts to `f` on the interior. -/
@[reassoc (attr := simp)]
lemma immersion_toBase_general {Y : Scheme.{u}} {f : Y ⟶ S} (j : CompactificationOf (Over.mk f)) :
    j.immersion ≫ j.toBase = f :=
  Over.w j.obj.hom

end CompactificationOf

namespace CategoryOfCompactifications

end CategoryOfCompactifications

end AlgebraicGeometry
