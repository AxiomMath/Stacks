module

public import StacksFrontier.AlgebraicGeometry.Blowup.Transform.Birational
public import StacksFrontier.AlgebraicGeometry.Blowup.Transform.Integral
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.QuadraticTransformations.PointBlowupChain
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalDoublePoints.SingularPointBlowupChain
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalSingularities.LerayFirstCohomologyExactness
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalSingularities.NormalizedBlowUpReduction

/-!
# Integrality of the stages of a chain of blowups in singular closed points

The blowup of an integral scheme `W` in a closed point `w` at which `W` is singular is integral
([Stacks, Tag 02ND]): the ideal of `w` is nonzero, since the generic point of `W` has a field as
local ring, hence is a regular point different from `w`. So every stage of a chain of blowups in
singular closed points over an integral scheme is integral. If moreover `W` is normal and
Noetherian, the blowup `b : W' ⟶ W` is a modification and `𝒪_W = b_*𝒪_{W'}`
([Stacks, Tag 0AY8]); this is used in the proof of the second sentence of [Stacks, Tag 0EA2].

## Main results

* `AlgebraicGeometry.DualizingDivisor.genericPoint_ne_of_mem_singularLocus`: a singular point of
  an integral scheme is not its generic point.
* `AlgebraicGeometry.DualizingDivisor.isIntegral_blowUp_of_mem_singularLocus`: the blowup in a
  singular closed point of an integral scheme is integral.
* `AlgebraicGeometry.DualizingDivisor.SingularPointBlowupChain.and_isIntegral`: the stages of a
  chain over an integral scheme are integral.
* `AlgebraicGeometry.DualizingDivisor.SingularPointBlowupChain.isModification`: such a chain over
  an integral Noetherian scheme is a modification.
* `AlgebraicGeometry.DualizingDivisor.isIso_c_blowUpToBase_of_mem_singularLocus`: `𝒪_W = b_*𝒪_{W'}`
  for the blowup `b` of a normal integral Noetherian `W` in a singular closed point.
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.DualizingDivisor

/-- **A singular point of an integral scheme is not its generic point**: the local ring at the
generic point is the function field, a regular local ring. -/
theorem genericPoint_ne_of_mem_singularLocus {W : Scheme.{u}} [IsIntegral W] {w : W}
    (hw : w ∈ singularLocus W) : genericPoint W ≠ w := by
  rintro rfl
  exact hw (inferInstanceAs (IsRegularLocalRing W.functionField))

/-- The ideal sheaf of a singular closed point of an integral scheme is nonzero. -/
theorem vanishingIdeal_ne_bot_of_mem_singularLocus {W : Scheme.{u}} [IsIntegral W] {w : W}
    (hw : IsClosed ({w} : Set W)) (hsing : w ∈ singularLocus W) :
    Scheme.IdealSheafData.vanishingIdeal (⟨{w}, hw⟩ : Closeds W) ≠ ⊥ :=
  vanishingIdeal_singleton_ne_bot w hw (genericPoint_ne_of_mem_singularLocus hsing)

/-- **The blowup of an integral scheme in a singular closed point is integral**
([Stacks, Tag 02ND]). -/
theorem isIntegral_blowUp_of_mem_singularLocus {W : Scheme.{u}} [IsIntegral W] {w : W}
    (hw : IsClosed ({w} : Set W)) (hsing : w ∈ singularLocus W) :
    IsIntegral (blowUp (Scheme.IdealSheafData.vanishingIdeal (⟨{w}, hw⟩ : Closeds W))) :=
  isIntegral_blowUp _ (vanishingIdeal_ne_bot_of_mem_singularLocus hw hsing)

/-- **The stages of a chain of blowups in singular closed points over an integral scheme are
integral**, so such a chain is a chain for the property `P W ∧ IsIntegral W`. -/
theorem SingularPointBlowupChain.and_isIntegral {P : Scheme.{u} → Prop} {X Y : Scheme.{u}}
    [IsIntegral X] {g : Y ⟶ X} (h : SingularPointBlowupChain P X Y g) :
    SingularPointBlowupChain (fun W => P W ∧ IsIntegral W) X Y g := by
  induction h with
  | refl hX => exact .refl ⟨hX, inferInstance⟩
  | step hh w hw hsing hP ih =>
    have : IsIntegral _ := ih.last.2
    exact ih.step w hw hsing ⟨hP, isIntegral_blowUp_of_mem_singularLocus hw hsing⟩

/-- **The blowup of an integral Noetherian scheme in a singular closed point is a
modification**: it is proper, birational since the centre is a nonzero ideal, and its source is
integral. -/
theorem isModification_blowUpToBase_of_mem_singularLocus {W : Scheme.{u}} [IsIntegral W]
    [IsNoetherian W] {w : W} (hw : IsClosed ({w} : Set W)) (hsing : w ∈ singularLocus W) :
    IsModification
      (blowUpToBase (Scheme.IdealSheafData.vanishingIdeal (⟨{w}, hw⟩ : Closeds W))) :=
  ⟨isBirational_blowUpToBase _ (vanishingIdeal_ne_bot_of_mem_singularLocus hw hsing),
    inferInstance, isIntegral_blowUp_of_mem_singularLocus hw hsing⟩

/-- **`𝒪_W = b_*𝒪_{W'}` for the blowup `b : W' ⟶ W` of a normal integral Noetherian scheme in a
singular closed point** ([Stacks, Tag 0AY8]): `b` is a modification of a normal integral
scheme. -/
theorem isIso_c_blowUpToBase_of_mem_singularLocus {W : Scheme.{u}} [IsIntegral W] [IsNormal W]
    [IsNoetherian W] {w : W} (hw : IsClosed ({w} : Set W)) (hsing : w ∈ singularLocus W) :
    IsIso (blowUpToBase
      (Scheme.IdealSheafData.vanishingIdeal (⟨{w}, hw⟩ : Closeds W))).toLRSHom.toHom.c :=
  (isModification_blowUpToBase_of_mem_singularLocus hw hsing).isIso_c_of_isNormal_target

/-- **A chain of blowups in singular closed points over an integral Noetherian scheme is a
modification**: every blowup in the chain is a modification of an integral Noetherian scheme,
and proper birational morphisms compose. -/
theorem SingularPointBlowupChain.isModification {P : Scheme.{u} → Prop} {X Y : Scheme.{u}}
    [IsIntegral X] [IsNoetherian X] {g : Y ⟶ X} (h : SingularPointBlowupChain P X Y g) :
    IsModification g := by
  have h' := SingularPointBlowupChain.and_isIntegral h
  clear h
  induction h' with
  | refl _ => exact isModification_id X
  | @step W k hh w hw hsing hP ih =>
    obtain ⟨hk, hkp, hW⟩ := ih
    have : IsProper k := hkp
    have : IsNoetherian W := Stacks.ResolutionOfSurfaces.isNoetherian_of_isProper_over_noetherian k
    exact ⟨(isModification_blowUpToBase_of_mem_singularLocus hw hsing).isBirational.comp hk,
      inferInstance, hP.2⟩

end AlgebraicGeometry.DualizingDivisor

end
