module

public import StacksFrontier.AlgebraicGeometry.Perfect.RelativeExtCanonical.PerfectStageBaseChangeCore
public import StacksFrontier.AlgebraicGeometry.Perfect.RelativeExtCanonical.TensorFlatBaseChangeNaturality
public import StacksFrontier.AlgebraicGeometry.Perfect.RelativeExtCanonical.FlatComplexBaseChange
public import StacksFrontier.AlgebraicGeometry.Perfect.DerivedPullbackPerfectGenerator
public import StacksFrontier.AlgebraicGeometry.Perfect.PerfectApproximation.Affine
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.PerfectDual

/-!
# Base change of the perfect stage along a cartesian square of schemes

For a cartesian square of schemes with `f` quasi-compact and quasi-separated and `𝒢^•` a bounded
complex of quasi-coherent modules flat over the base, the base-change map of
[Stacks, Tag 0A1D] — with the ordinary pullback `(g')^*𝒢^•` — is invertible at the dual of every
perfect object and natural, so the constructions of
`StacksFrontier.AlgebraicGeometry.Perfect.RelativeExtCanonical.PerfectStageBaseChangeCore` apply to
it: `Lg^*K(P) ≅ K'(L(g')^*P)` and `Lg^*L(P) ≅ L'(L(g')^*P)`, naturally in `P`.

All statements are at the standard model, through
`Stacks.Cohomology.RelativeExtCanonical.StdDerivedModules` and `IsPerfectStd`.

## Main definitions

* `Stacks.Cohomology.RelativeExtCanonical.squareStageKIso`
* `Stacks.Cohomology.RelativeExtCanonical.squareStageLIso`
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry
open RingedSpaceModuleAdjunction TopologicalSpace
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPullback derivedPushforward)
open Stacks.Cohomology.DerivedPullbackTensor (pullbackComplex)

universe u

namespace Stacks.Cohomology.RelativeExtCanonical

open Stacks.Cohomology.RelativeExt

variable {X S S' X' : Scheme.{u}} {f : X ⟶ S} {g : S' ⟶ S} {f' : X' ⟶ S'} {g' : X' ⟶ X}
  (hsq : IsPullback g' f' f g)
  {G : CochainComplex (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) ℤ}

include hsq in
/-- The commutative square of ringed spaces underlying the cartesian square. -/
theorem toShHom_comm :
    g'.toLRSHom.toShHom ≫ f.toLRSHom.toShHom = f'.toLRSHom.toShHom ≫ g.toLRSHom.toShHom :=
  congrArg (fun h : X' ⟶ S => h.toLRSHom.toShHom) hsq.w

variable (G) in
/-- The base-change map of [Stacks, Tag 0A1D], as the family the constructions of
`PerfectStageBaseChangeCore` take. -/
def squareBaseChangeMap :
    BaseChangeFamily f.toLRSHom.toShHom g.toLRSHom.toShHom f'.toLRSHom.toShHom g'.toLRSHom.toShHom
      G ((pullbackComplex g'.toLRSHom.toShHom).obj G) :=
  fun E ↦ tensorFlatBaseChangeMap f g f' g' (toShHom_comm hsq) E G

/-- The base-change map of [Stacks, Tag 0A1D] is natural, in the form
`PerfectStageBaseChangeCore` takes. -/
theorem squareBaseChangeMap_isNatural : (squareBaseChangeMap hsq G).IsNatural :=
  fun e ↦ tensorFlatBaseChangeMap_naturality f g f' g' (toShHom_comm hsq) e G

include hsq in
/-- The base-change map of [Stacks, Tag 0A1D] is invertible at the dual of a perfect object. -/
theorem isIso_squareBaseChangeMap [QuasiCompact f] [QuasiSeparated f]
    (hG : IsBoundedFlatOver f.toLRSHom.toShHom G) (hGq : ∀ i : ℤ, (G.X i).IsQuasicoherent)
    (P : StdDerivedModules X.sheaf) (hP : IsPerfectStd P) :
    IsIso (squareBaseChangeMap hsq G (Stacks.SheafOfModules.derivedDual X.sheaf P)) := by
  have hD := Stacks.SheafOfModules.isPerfect_derivedDual X.sheaf P hP
  refine isIso_tensorFlatBaseChangeMap_of_isPullback f g f' g' hsq inferInstance inferInstance
    (toShHom_comm hsq) _ (fun n ↦ PerfectApproximation.isQuasicoherent_homology_of_isPerfect X _
      (@Stacks.Cohomology.PerfectComplexes.isPerfect_of_ringedSite X.toRingedSpace
        (HasDerivedCategory.standard _) _ hD) n) G
    ?_ hGq hG.isFlatOver
  obtain ⟨a, b, -, hb⟩ := hG.bounded
  exact ⟨b, hb⟩

/-- The derived pullback of a perfect object along a morphism of schemes is perfect. -/
theorem isPerfectStd_stdPullback {Y Z : Scheme.{u}} (h : Y ⟶ Z) (P : StdDerivedModules Z.sheaf)
    (hP : IsPerfectStd P) : IsPerfectStd ((stdPullback h.toLRSHom.toShHom).obj P) :=
  isPerfect_ringedSite_derivedPullback h P hP

end Stacks.Cohomology.RelativeExtCanonical

end
