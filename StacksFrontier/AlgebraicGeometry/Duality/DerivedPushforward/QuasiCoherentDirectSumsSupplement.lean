module

public import StacksFrontier.AlgebraicGeometry.Duality.DerivedPushforward.QuasiCoherentDirectSums
public import StacksFrontier.Algebra.Homology.DerivedCategory.TruncationLevelHomology
public import StacksFrontier.AlgebraicGeometry.AffineBaseChange.Basic
public import StacksFrontier.AlgebraicGeometry.DerivedAcyclic.Pushforward
public import StacksFrontier.AlgebraicGeometry.Duality.DerivedPushforward.BoundedDirectSums
public import StacksFrontier.AlgebraicGeometry.Duality.DerivedPushforward.DirectSums
public import StacksFrontier.AlgebraicGeometry.Duality.RightAdjointBoundedBelow
public import StacksFrontier.AlgebraicGeometry.TotalDirectImage.QuasiCoherentDirectImage
public import StacksFrontier.Homology.PseudoCoherent.Locality
import StacksCore.Tactic.StacksAttribute

/-!
# Further results on `QuasiCoherentDirectSums`

Results about the objects of
`StacksFrontier.AlgebraicGeometry.Duality.DerivedPushforward.QuasiCoherentDirectSums` that need
imports beyond those of that module.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open TopologicalSpace

universe w u v₁ u₁ v₂ u₂

namespace Stacks.Duality.DerivedPushforward

attribute [local instance 10000] HasDerivedCategory.standard

attribute [local instance]
  Stacks.SmallDerivedCategory.hasColimitsOfShape_discrete_derivedCategory

attribute [local instance] AlgebraicGeometry.pullback_preservesFiniteLimits_of_isOpenImmersion

section Pullback

variable {S V : Scheme.{u}} (j : V ⟶ S) [IsOpenImmersion j]

/-- Pullback along an open immersion of the target, on unbounded derived categories at an
arbitrary chosen model of the two. It is exact, so no derivation is involved.

The model is a binder rather than the `CategoryTheory.HasDerivedCategory.standard` in force in
the rest of this file, because nothing here needs a pin: pullback along an open immersion is
exact at every model, and
`StacksFrontier/AlgebraicGeometry/Duality/DerivedPushforward/QcohDirectSumsAnyModel.lean` asks for
this same functor at the locally small model instead. Inside this file instance search resolves
the binder to `standard`, whose `local instance` declaration above has priority `10000`. -/
abbrev derivedPullbackOpenAtModel [HasDerivedCategory.{w} S.Modules]
    [HasDerivedCategory.{w} V.Modules] :
    DerivedCategory S.Modules ⥤ DerivedCategory V.Modules :=
  (Scheme.Modules.pullback j).mapDerivedCategory

end Pullback

section Local

variable {X S : Scheme.{u}} (f : X ⟶ S) {V : Scheme.{u}} (j : V ⟶ S) [IsOpenImmersion j]

/-- The derived direct image along `f`, followed by pullback to an open `V ⊆ S`, at an arbitrary
chosen model of the three derived categories. By [Stacks, Tag 08FE] this is the derived direct
image along the restricted morphism `f⁻¹V ⟶ V`, which is what gives it a uniform cohomological
bound when `V` is quasi-compact — and that bound, unlike the functor, is available only at
`CategoryTheory.HasDerivedCategory.standard`, which is what instance search resolves the binder
to inside this file. -/
abbrev derivedPushforwardPullbackAtModel [HasDerivedCategory.{w} X.Modules]
    [HasDerivedCategory.{w} S.Modules] [HasDerivedCategory.{w} V.Modules] :
    DerivedCategory X.Modules ⥤ DerivedCategory V.Modules :=
  Stacks.Duality.derivedPushforward f ⋙ derivedPullbackOpenAtModel.{w} j

end Local

variable {X S : Scheme.{u}} (f : X ⟶ S) [AlgebraicGeometry.QuasiCompact f]
  [AlgebraicGeometry.QuasiSeparated f]

end Stacks.Duality.DerivedPushforward

end
