module

public import StacksFrontier.AlgebraicGeometry.Perfect.RelativeExtCanonical.HocolimUnit
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.DerivedPullbackTopDegree
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.AdjunctionUnconditional
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.Triangulated

/-!
# Derived pullback of a homotopy colimit, and of a truncation isomorphism

For a morphism of ringed spaces `f : X ⟶ Y`, the derived pullback `Lf^*` is a triangulated left
adjoint, so it carries a homotopy colimit of a system indexed by `ℕ` to the homotopy colimit of
the pulled back system, with the pulled back coprojections. It is right t-exact, so a map
inducing an isomorphism on `τ_{≥ k}` is carried to one inducing an isomorphism on `τ_{≥ k + 1}`.

These are the two facts by which the approximation of [Stacks, Tag 08IF] (B) is carried along a
base change in [Stacks, Tag 0DJS].

## Main results

* `Stacks.Cohomology.RelativeExtCanonical.isHomotopyColimitWith_derivedPullback`
* `Stacks.Cohomology.RelativeExtCanonical.isIso_truncGE_map_derivedPullback`
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated AlgebraicGeometry

universe u


namespace Stacks.Cohomology.RelativeExtCanonical

open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPullback derivedAdjunction)

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)

/-- **Derived pullback carries a homotopy colimit to a homotopy colimit**, with the pulled back
coprojections. Stated at the standard model of both derived categories, the model of the
triangulated structure of `Lf^*`. -/
theorem isHomotopyColimitWith_derivedPullback :
    letI := HasDerivedCategory.standard (SheafOfModules.{u} (structureSheafRing Y))
    letI := HasDerivedCategory.standard (SheafOfModules.{u} (structureSheafRing X))
    ∀ {F : ℕ ⥤ DerivedCategory (SheafOfModules.{u} (structureSheafRing Y))}
      [HasCoproduct F.obj] {K : DerivedCategory (SheafOfModules.{u} (structureSheafRing Y))}
      {c : ∀ n, F.obj n ⟶ K} (_ : IsHomotopyColimitWith F K c)
      [HasCoproduct (F ⋙ derivedPullback f).obj],
      IsHomotopyColimitWith (F ⋙ derivedPullback f) ((derivedPullback f).obj K)
        (fun n ↦ (derivedPullback f).map (c n)) := by
  let := HasDerivedCategory.standard (SheafOfModules.{u} (structureSheafRing Y))
  let := HasDerivedCategory.standard (SheafOfModules.{u} (structureSheafRing X))
  intro F _ K c h _
  let : (derivedPullback f).CommShift ℤ :=
    Stacks.Cohomology.KFlatDerivedPullback.derivedPullback_commShift f
  have : (derivedPullback f).IsTriangulated :=
    Stacks.Cohomology.KFlatDerivedPullback.derivedPullback_isTriangulated f
  have : PreservesColimit (Discrete.functor F.obj) (derivedPullback f) :=
    (derivedAdjunction f).leftAdjoint_preservesColimits.preservesColimitsOfShape
      |>.preservesColimit
  exact h.map (derivedPullback f)

/-- **Derived pullback shifts truncation isomorphisms by one degree.** If `φ` induces an
isomorphism on `τ_{≥ k}`, then `Lf^* φ` induces one on `τ_{≥ k + 1}`. Stated at the standard
model, the model of the right t-exactness of `Lf^*`. -/
theorem isIso_truncGE_map_derivedPullback :
    letI := HasDerivedCategory.standard (SheafOfModules.{u} (structureSheafRing Y))
    letI := HasDerivedCategory.standard (SheafOfModules.{u} (structureSheafRing X))
    ∀ {A B : DerivedCategory (SheafOfModules.{u} (structureSheafRing Y))} (φ : A ⟶ B) (k : ℤ),
      IsIso ((DerivedCategory.TStructure.t.truncGE k).map φ) →
      IsIso ((DerivedCategory.TStructure.t.truncGE (k + 1)).map ((derivedPullback f).map φ)) := by
  let := HasDerivedCategory.standard (SheafOfModules.{u} (structureSheafRing Y))
  let := HasDerivedCategory.standard (SheafOfModules.{u} (structureSheafRing X))
  intro A B φ k h
  let : (derivedPullback f).CommShift ℤ :=
    Stacks.Cohomology.KFlatDerivedPullback.derivedPullback_commShift f
  have : (derivedPullback f).IsTriangulated :=
    Stacks.Cohomology.KFlatDerivedPullback.derivedPullback_isTriangulated f
  exact isIso_truncGE_map_of_isLE_preserving (derivedPullback f)
    (fun X j hX ↦ Stacks.AlgebraicGeometry.TopDegreeBaseChange.isLE_derivedPullback_obj
      f X j hX) φ k h

end Stacks.Cohomology.RelativeExtCanonical

end
