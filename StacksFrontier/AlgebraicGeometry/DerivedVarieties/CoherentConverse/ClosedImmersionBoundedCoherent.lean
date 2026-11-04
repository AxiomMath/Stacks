module

public import StacksFrontier.AlgebraicGeometry.DerivedAffineMorphism.PushforwardTExactness
public import StacksFrontier.AlgebraicGeometry.DerivedAffineMorphism.ReflectsIsomorphismsAffineHom
public import StacksFrontier.AlgebraicGeometry.CoherentPushforwardCriteria.ClosedImmersionCoherence
public import StacksFrontier.AlgebraicGeometry.ProperSupportCoherent.DerivedDirectImage
public import StacksFrontier.AlgebraicGeometry.ClosedPushforward.Coherent

/-!
# Derived direct image along a closed immersion reflects `D^b_Coh`

Let `c : U ⟶ V` be a closed immersion into a locally Noetherian scheme and `K` an object of
`D(𝒪_U)` with quasi-coherent cohomology. If `Rc_*K` lies in `D^b_Coh(𝒪_V)` then `K` lies in
`D^b_Coh(𝒪_U)`.

## Main results

* `derivedCategoryBBounded_of_derivedPushforward`: if `Rc_*K` lies in `D^b_Coh(𝒪_V)`, then `K`
  lies in `D^b_Coh(𝒪_U)`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces

universe u

attribute [local instance 10000] HasDerivedCategory.standard

namespace Stacks.AlgebraicGeometry.ClosedImmersionBoundedCoherent

variable {U V : Scheme.{u}} (c : U ⟶ V) [IsClosedImmersion c] [IsLocallyNoetherian V]

/-- **Derived direct image along a closed immersion reflects `D^b_Coh`**, for complexes with
quasi-coherent cohomology. -/
theorem derivedCategoryBBounded_of_derivedPushforward
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing U.toRingedSpace)))
    (hq : ∀ i : ℤ, ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (structureSheafRing U.toRingedSpace)) i).obj K).IsQuasicoherent)
    (h : DerivedCategoryB.derivedCategoryBBounded
      (fun M : SheafOfModules.{u} (structureSheafRing V.toRingedSpace) => M.IsCoherent)
      ((derivedPushforward c.toLRSHom.toShHom).obj K)) :
    DerivedCategoryB.derivedCategoryBBounded
      (fun M : SheafOfModules.{u} (structureSheafRing U.toRingedSpace) => M.IsCoherent) K := by
  have : IsLocallyNoetherian U := isLocallyNoetherian_of_isClosedImmersion c
  obtain ⟨⟨⟨a, ha⟩, ⟨b, hb⟩⟩, hc⟩ := h
  have hz : ∀ i, IsZero ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (structureSheafRing V.toRingedSpace)) i).obj
        ((derivedPushforward c.toLRSHom.toShHom).obj K)) →
      IsZero ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (structureSheafRing U.toRingedSpace)) i).obj K) := fun i h0 =>
    Stacks.AlgebraicGeometry.AffinePushforwardTExactness.isZero_of_isZero_pushforward_of_isAffineHom
      c _ (hq i) (h0.of_iso
        (Stacks.AlgebraicGeometry.AffinePushforwardTExactness.homologyDerivedPushforwardIso
          c K hq i).symm)
  exact ⟨⟨⟨a, fun i hi => hz i (ha i hi)⟩, ⟨b, fun i hi => hz i (hb i hi)⟩⟩, fun i =>
    (@Stacks.AlgebraicGeometry.ClosedImmersionCoherence.isCoherent_pushforward_iff U V _ _ c _
      _ (hq i)).1 <| (Stacks.AlgebraicGeometry.ProperSupportCoherent.isCoherent_isWeakSerre
        V).isClosedUnderIsomorphisms.of_iso
          (Stacks.AlgebraicGeometry.AffinePushforwardTExactness.homologyDerivedPushforwardIso
            c K hq i) (hc i)⟩

end Stacks.AlgebraicGeometry.ClosedImmersionBoundedCoherent

end
