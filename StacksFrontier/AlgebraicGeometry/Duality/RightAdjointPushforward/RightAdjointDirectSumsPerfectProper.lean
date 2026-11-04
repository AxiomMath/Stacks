module

public import StacksFrontier.AlgebraicGeometry.Duality.RightAdjointPushforward.RightAdjointDirectSums
public import StacksFrontier.AlgebraicGeometry.Duality.CompactGeneration.CompactPerfect
public import StacksFrontier.AlgebraicGeometry.Duality.CompactGeneration.QcqsCompactGeneration
public import StacksFrontier.AlgebraicGeometry.Duality.DerivedPushforward.Exactness
public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizingModule
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.PerfectMorphism.PerfectDirectImageLocallySmall
public import StacksFrontier.CategoryTheory.Triangulated.RightAdjointCoproducts
public import StacksFrontier.CategoryTheory.Triangulated.RightAdjointCoproductsFamily

/-!
# Right adjoints of direct images along perfect proper morphisms

Let `f : X ⟶ Y` be a morphism of schemes with `X` quasi-compact and quasi-separated. If
`Rf_* : D_QCoh(𝒪_X) ⥤ D_QCoh(𝒪_Y)` preserves compact objects, then every right adjoint of `Rf_*`
commutes with direct sums. For `f` perfect and proper between Noetherian schemes, `Rf_*` preserves
compact objects, so its right adjoint, the twisted inverse image `f^×`, commutes with direct sums.

## Main results

* `preservesColimitsOfShape_rightAdjoint_of_isCompactObject_map`: a right adjoint of `Rf_*`
  commutes with direct sums when `Rf_*` preserves compact objects.
* `isCompactObject_quasiCoherentDerivedPushforward`: for `f` perfect and proper between Noetherian
  schemes, `Rf_*` preserves compact objects.
* `preservesColimitsOfShape_rightAdjoint_quasiCoherentDerivedPushforward`: for `f` perfect and
  proper between Noetherian schemes, a right adjoint of `Rf_*` commutes with direct sums.
* `preservesColimitsOfShape_twistedInverseImage`: for `f` perfect and proper between Noetherian
  schemes, `f^×` commutes with direct sums.
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for sheaves of modules on a small site.
-- `D(𝒪_X)` for a scheme.
attribute [local instance] SheafOfModules.hasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.ObjectProperty
open Stacks.Duality.DerivedPushforward

universe u

namespace Stacks.Duality

variable {X Y : Scheme.{u}} (f : X ⟶ Y)
  (hpush : ∀ (K : quasiCoherentDerivedCategory X) (i : ℤ),
    ((DerivedCategory.homologyFunctor Y.Modules i).obj
      ((derivedPushforward f).obj K.obj)).IsQuasicoherent)

/-! ### The reduction to compactness of direct images -/

/-- **A right adjoint of `Rf_*` commutes with direct sums as soon as `Rf_*` preserves compact
objects.** Let `f : X ⟶ Y` with `X` quasi-compact and quasi-separated, so that `D_QCoh(𝒪_X)` is
compactly generated ([Stacks, Tag 09IS]); if `Rf_*` carries compact objects of `D_QCoh(𝒪_X)` to
compact objects of `D_QCoh(𝒪_Y)`, every right adjoint of `Rf_*` commutes with direct sums. This
is the formal half of the proof of [Stacks, Tag 0A9R]. -/
theorem preservesColimitsOfShape_rightAdjoint_of_isCompactObject_map [CompactSpace X]
    [QuasiSeparatedSpace X] {a : quasiCoherentDerivedCategory Y ⥤ quasiCoherentDerivedCategory X}
    (adj : quasiCoherentDerivedPushforward f hpush ⊣ a)
    (hcomp : ∀ E : quasiCoherentDerivedCategory X, IsCompactObject.{u} E →
      IsCompactObject.{u} ((quasiCoherentDerivedPushforward f hpush).obj E))
    (J : Type u) : PreservesColimitsOfShape (Discrete J) a := by
  obtain ⟨ι, E, hEc, hE⟩ := QcqsGeneration.isCompactlyGenerated_quasiCoherentDerivedCategory X
  have hsumX := hasCoproducts_quasiCoherentDerivedCategory X
  have hsumY := hasCoproducts_quasiCoherentDerivedCategory Y
  have hadd : a.Additive := adj.right_adjoint_additive
  exact Pretriangulated.preservesColimitsOfShape_discrete_of_isCompactObject_map_ofObj adj E hE
    hEc (fun i => hcomp _ (hEc i)) J

/-- **Direct image of a compact object along a perfect proper morphism is perfect.** For
`f : X ⟶ Y` perfect and proper with `X` and `Y` Noetherian, `Rf_*` carries a compact object of
`D_QCoh(𝒪_X)` to a perfect object of `D(𝒪_Y)`: a compact object is perfect
([Stacks, Tag 09M1]) and `Rf_*` preserves perfectness ([Stacks, Tag 0B6G]). -/
theorem isPerfect_quasiCoherentDerivedPushforward_of_isCompactObject [IsNoetherian X]
    [IsNoetherian Y] [Perfect f] [IsProper f] (E : quasiCoherentDerivedCategory X)
    (hE : IsCompactObject.{u} E) :
    Stacks.Cohomology.PerfectComplexes.IsPerfect (X := Y.toRingedSpace)
      ((quasiCoherentDerivedPushforward f hpush).obj E).obj :=
  AlgebraicGeometry.PerfectProperDirectImage.isPerfect_derivedPushforward_of_isPerfect_locallySmall
    f E.obj (isPerfect_of_isCompactObject E hE)

/-! ### The right adjoint commutes with direct sums -/

/-- **Direct image along a perfect proper morphism preserves compact objects.** For
`f : X ⟶ Y` perfect and proper with `X` and `Y` Noetherian, `Rf_*` carries compact objects of
`D_QCoh(𝒪_X)` to compact objects of `D_QCoh(𝒪_Y)`. -/
theorem isCompactObject_quasiCoherentDerivedPushforward [IsNoetherian X] [IsNoetherian Y]
    [Perfect f] [IsProper f] (E : quasiCoherentDerivedCategory X) (hE : IsCompactObject.{u} E) :
    IsCompactObject.{u} ((quasiCoherentDerivedPushforward f hpush).obj E) :=
  isCompactObject_of_isPerfect _ (isPerfect_quasiCoherentDerivedPushforward_of_isCompactObject f
    hpush E hE)

/-- A right adjoint of `Rf_*` commutes with direct sums, for any proof `hpush` that `Rf_*`
preserves quasi-coherence of cohomology, when `f : X ⟶ Y` is a perfect proper morphism of
Noetherian schemes. -/
theorem preservesColimitsOfShape_rightAdjoint_quasiCoherentDerivedPushforward_of_hpush
    [IsNoetherian X] [IsNoetherian Y] [Perfect f] [IsProper f]
    {a : quasiCoherentDerivedCategory Y ⥤ quasiCoherentDerivedCategory X}
    (adj : quasiCoherentDerivedPushforward f hpush ⊣ a) (J : Type u) :
    PreservesColimitsOfShape (Discrete J) a :=
  preservesColimitsOfShape_rightAdjoint_of_isCompactObject_map f hpush adj
    (isCompactObject_quasiCoherentDerivedPushforward f hpush) J

omit hpush in
/-- Let `f : X ⟶ Y` be a perfect proper morphism of Noetherian schemes and let `a` be a right
adjoint of `Rf_* : D_QCoh(𝒪_X) ⥤ D_QCoh(𝒪_Y)`. Then `a` commutes with direct sums. -/
@[stacks 0A9R]
theorem preservesColimitsOfShape_rightAdjoint_quasiCoherentDerivedPushforward [IsNoetherian X]
    [IsNoetherian Y] [Perfect f] [IsProper f]
    {a : quasiCoherentDerivedCategory Y ⥤ quasiCoherentDerivedCategory X}
    (adj : quasiCoherentDerivedPushforward f
      (isQuasicoherent_homology_derivedPushforward_of_qcqs f) ⊣ a) (J : Type u) :
    PreservesColimitsOfShape (Discrete J) a :=
  preservesColimitsOfShape_rightAdjoint_quasiCoherentDerivedPushforward_of_hpush f _ adj J

/-- For a perfect proper morphism of Noetherian schemes `f : X ⟶ Y`, the twisted inverse image
`f^× : D_QCoh(𝒪_Y) ⥤ D_QCoh(𝒪_X)`, the right adjoint `twistedInverseImage f` of `Rf_*`, commutes
with direct sums. -/
@[stacks 0A9R]
instance preservesColimitsOfShape_twistedInverseImage [IsNoetherian X] [IsNoetherian Y]
    [Perfect f] [IsProper f] (J : Type u) :
    PreservesColimitsOfShape (Discrete J)
      (twistedInverseImage f (isQuasicoherent_homology_derivedPushforward_of_qcqs f)) :=
  preservesColimitsOfShape_rightAdjoint_quasiCoherentDerivedPushforward f
    (twistedInverseImageAdjunction f _) J

end Stacks.Duality

end
