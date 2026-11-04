module

public import StacksFrontier.AlgebraicGeometry.Duality.TwistedInverseImage.BoundedBelow
public import StacksFrontier.AlgebraicGeometry.Duality.CompactGeneration.QcqsCompactGeneration
import StacksFrontier.AlgebraicGeometry.Duality.DerivedPushforward.UniformBoundAnyModel
public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizingModule
import StacksFrontier.AlgebraicGeometry.Duality.RightAdjointBoundedBelow
public import StacksFrontier.AlgebraicGeometry.QuasiCoherent.Coherator.QcqsPushforwardAnyModel

/-!
# Further results

Results complementing `StacksFrontier.AlgebraicGeometry.Duality.TwistedInverseImage.BoundedBelow`.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe w u

namespace Stacks.Duality

/-- `D⁺_QCoh(𝒪_Z)`: the full subcategory of the quasi-coherent derived category of a scheme on the
objects with bounded-below cohomology. The exceptional inverse image of [Stacks, Tag 0AA0] is a
functor between these categories. -/
abbrev quasiCoherentDerivedCategoryPlusOfModel (Z : Scheme.{u}) [HasDerivedCategory.{w} Z.Modules] :
    Type (u + 1) :=
  ObjectProperty.FullSubcategory
    (fun K : quasiCoherentDerivedCategory Z => DerivedCategoryB.IsBoundedBelow K.obj)

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [CompactSpace X] [QuasiSeparatedSpace X]
  [CompactSpace Y] [QuasiSeparatedSpace Y]

end Stacks.Duality

end
