module

public import StacksFrontier.AlgebraicGeometry.Duality.SingleQuasiCoherent
public import StacksFrontier.AlgebraicGeometry.Duality.TwistedInverseImage.CompositionExtra
public import StacksFrontier.AlgebraicGeometry.Duality.TwistedInverseImageFTS.Basic
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalDoublePoints.SingularPointBlowupChain
public import StacksFrontier.AlgebraicGeometry.Blowup.Proper

/-!
# Trivial twisted inverse image along a chain of blowups

A proper morphism `f : X ⟶ Y` with `Y` Noetherian *has trivial twisted inverse image* when
`f^×(𝒪_Y[0]) ≅ 𝒪_X[0]` in `D_QCoh(𝒪_X)`. The property holds for identities and is stable under
composition (`(f ≫ g)^× ≅ g^× ⋙ f^×`, [Stacks, Tag 0ATX]), so it holds along a chain of blowups
in singular closed points (Situation of [Stacks, Tag 0BGE]) as soon as it holds for each blowup in
the chain. This is the induction step of the proof of the second sentence of
[Stacks, Tag 0EA2].

## Main definitions

* `AlgebraicGeometry.DualizingDivisor.HasTrivialTwistedInverseImage f`: `f^×(𝒪_Y[0]) ≅ 𝒪_X[0]`.

## Main results

* `AlgebraicGeometry.DualizingDivisor.SingularPointBlowupChain.hasTrivialTwistedInverseImage`:
  the property along a chain of blowups, given it for each blowup of a stage of the chain.
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(𝒪_X)` for a scheme.
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public section

open CategoryTheory Stacks.Duality

universe u

namespace AlgebraicGeometry.DualizingDivisor

/-- The structure sheaf placed in degree zero, as an object of `D_QCoh(𝒪_X)`. -/
noncomputable abbrev unitQC (X : Scheme.{u}) : quasiCoherentDerivedCategory X :=
  singleQuasiCoherent (SheafOfModules.unit X.ringCatSheaf)
    inferInstance 0

/-- **A proper morphism with trivial twisted inverse image**: `f^×(𝒪_Y[0]) ≅ 𝒪_X[0]` in
`D_QCoh(𝒪_X)`, for `f^×` the right adjoint of `Rf_*` on `D_QCoh` ([Stacks, Tag 0A9E]). -/
def HasTrivialTwistedInverseImage {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f]
    [QuasiSeparated f] [CompactSpace Y] : Prop :=
  letI := isLeftAdjoint_qcqsQuasiCoherentDerivedPushforward f
  Nonempty ((twistedInverseImage f (isQuasicoherent_homology_derivedPushforward_of_qcqs f)).obj
    (unitQC Y) ≅ unitQC X)

/-- The identity has trivial twisted inverse image (`Stacks.Duality.twistedInverseImageIdIso`). -/
theorem hasTrivialTwistedInverseImage_id (X : Scheme.{u}) [CompactSpace X] :
    HasTrivialTwistedInverseImage (𝟙 X) :=
  ⟨(twistedInverseImageIdIso X _).app _⟩

/-- **Trivial twisted inverse image is stable under composition**, by
`(f ≫ g)^× ≅ g^× ⋙ f^×` ([Stacks, Tag 0ATX], `Stacks.Duality.twistedInverseImageCompIsoOfQcqs`). -/
theorem HasTrivialTwistedInverseImage.comp {X Y Z : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
    [QuasiCompact f] [QuasiSeparated f] [QuasiCompact g] [QuasiSeparated g] [CompactSpace Y]
    [CompactSpace Z] (hf : HasTrivialTwistedInverseImage f)
    (hg : HasTrivialTwistedInverseImage g) : HasTrivialTwistedInverseImage (f ≫ g) := by
  let := isLeftAdjoint_qcqsQuasiCoherentDerivedPushforward f
  let := isLeftAdjoint_qcqsQuasiCoherentDerivedPushforward g
  let := isLeftAdjoint_qcqsQuasiCoherentDerivedPushforward (f ≫ g)
  obtain ⟨ef⟩ := hf
  obtain ⟨eg⟩ := hg
  exact ⟨(twistedInverseImageCompIsoOfQcqs f g).app _ ≪≫
    (twistedInverseImage f (isQuasicoherent_homology_derivedPushforward_of_qcqs f)).mapIso eg ≪≫
      ef⟩

/-- **Trivial twisted inverse image along a chain of blowups in singular closed points.** Let
`X` be Noetherian and `g : Y ⟶ X` a chain of blowups in singular closed points
(`SingularPointBlowupChain`). If the blowup of every Noetherian stage `W` of the chain in a
singular closed point `w` has trivial twisted inverse image, then so does `g`; every stage is
Noetherian and proper over `X`. -/
theorem SingularPointBlowupChain.hasTrivialTwistedInverseImage {P : Scheme.{u} → Prop}
    {X Y : Scheme.{u}} [IsNoetherian X] {g : Y ⟶ X} (hg : SingularPointBlowupChain P X Y g)
    (hstage : ∀ (W : Scheme.{u}) [IsNoetherian W], P W → ∀ (w : W) (hw : IsClosed ({w} : Set W)),
      w ∈ singularLocus W →
        HasTrivialTwistedInverseImage
          (blowUpToBase (Scheme.IdealSheafData.vanishingIdeal ⟨{w}, hw⟩))) :
    ∃ (_ : IsProper g) (_ : IsNoetherian Y), HasTrivialTwistedInverseImage g := by
  induction hg with
  | refl hX => exact ⟨inferInstance, inferInstance, hasTrivialTwistedInverseImage_id X⟩
  | @step W h hh w hw hsing hP ih =>
    obtain ⟨_, _, ih⟩ := ih
    have hb := hstage W hh.last w hw hsing
    have : IsNoetherian (blowUp (Scheme.IdealSheafData.vanishingIdeal ⟨{w}, hw⟩)) :=
      have := LocallyOfFiniteType.isLocallyNoetherian
        (blowUpToBase (Scheme.IdealSheafData.vanishingIdeal ⟨{w}, hw⟩))
      have : CompactSpace (blowUp (Scheme.IdealSheafData.vanishingIdeal ⟨{w}, hw⟩)) :=
        QuasiCompact.compactSpace_of_compactSpace
          (blowUpToBase (Scheme.IdealSheafData.vanishingIdeal ⟨{w}, hw⟩))
      ⟨⟩
    exact ⟨inferInstance, inferInstance, hb.comp ih⟩

end AlgebraicGeometry.DualizingDivisor
